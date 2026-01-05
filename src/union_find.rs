use std::{
    cell::UnsafeCell,
    fmt::Debug,
    mem,
    sync::{RwLock, atomic::{AtomicUsize, Ordering}},
};

use crate::{
    numbers::{I, Int},
    permutations::Permutation,
};

/// Metadata about each disjoint set
pub trait SetInfo {
    /// Merge the info for two sets, used on the `union` call. Return the path info for the new child.
    fn merge(&mut self, new_child: Self);
}

/// Information about the path taken from a node to its representative
pub trait PathInfo {
    /// Join a path with the path of its parent. This function must be associative.
    fn join_paths(path: &mut Self, path_of_parent: &Self);

    /// Trim the prefix from the beginning of the path. Can also be thought of as pre-applying the inverse.
    fn remove_prefix(path: &mut Self, prefix: &Self);
}

impl SetInfo for () {
    fn merge(&mut self, (): Self) {}
}

impl PathInfo for () {
    fn join_paths((): &mut Self, (): &Self) {}

    fn remove_prefix((): &mut Self, (): &Self) {}
}

/// A `SetInfo` implementor that counts the cardinality of each set
#[derive(Debug, Clone, Copy)]
pub struct Cardinality(pub usize);

impl Default for Cardinality {
    fn default() -> Self {
        Self(1)
    }
}

impl SetInfo for Cardinality {
    fn merge(&mut self, new_child: Self) {
        self.0 += new_child.0;
    }
}

/// Composes permutations along the path
impl PathInfo for Permutation {
    fn join_paths(path: &mut Self, path_of_parent: &Self) {
        path.compose_into(path_of_parent);
    }

    fn remove_prefix(path: &mut Self, prefix: &Self) {
        let mut inv = prefix.to_owned();
        inv.invert();
        inv.compose_into(path);
        *path = inv;
    }
}

enum UnionFindEntry<S: SetInfo, P: PathInfo> {
    RootOfSet { set_meta: S },
    // Tuple of (owned by, path info)
    // Invariants of the UnsafeCell: In every situation, the UnsafeCell is treated as an immutable location and a mutable reference is only taken in one location (path compression). That location has the proof that it's valid.
    OwnedBy { owned_by: AtomicUsize, path_info: UnsafeCell<P> },
}

// SAFETY: We are requiring that `S` and `P` be `Sync`, and we have synchronization for the `UnsafeCell`.
// TODO: Change to `SyncUnsafeCell` once that's stabilized.
unsafe impl<S: SetInfo + Sync, P: PathInfo + Sync> Sync for UnionFindEntry<S, P> {}

/// A data structure allowing you track disjoint sets of numbers. In puzzle-theory, this means orbits in a permutation group but you can use it for anything.
///
/// This structure also keeps track of metadata for each set and element. If you do not need this, use `()` for the `S` parameter.
pub struct UnionFind<S: SetInfo, P: PathInfo> {
    sets: Box<[UnionFindEntry<S, P>]>,
    compression_lock: RwLock<()>,
}

impl<S: SetInfo + Debug, P: PathInfo + Debug> Debug for UnionFind<S, P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for i in 0..self.sets.len() {
            let find_info = self.find(i);
            write!(f, "{i} → {} | ", find_info.root_idx())?;
            match find_info.path_meta() {
                Some(path) => path.fmt(f)?,
                None => find_info.set_meta().fmt(f)?,
            }
            writeln!(f)?;
        }

        Ok(())
    }
}

/// Information about an element, returned by the `find` operation
#[derive(Debug)]
pub struct FindResult<'a, S: SetInfo, P: PathInfo> {
    root_idx: usize,
    set_meta: &'a S,
    path_meta: Option<&'a P>,
}

impl<'a, S: SetInfo, P: PathInfo> FindResult<'a, S, P> {
    /// Returns the index of the element representing the root of the set
    #[must_use]
    pub fn root_idx(&self) -> usize {
        self.root_idx
    }

    /// Metadata associated with the set the element is a member of
    #[must_use]
    pub fn set_meta(&self) -> &S {
        self.set_meta
    }

    /// Metadata associated with the path from this element to the root
    #[must_use]
    pub fn path_meta(&self) -> Option<&'a P> {
        self.path_meta
    }
}

impl<S: SetInfo + Default, P: PathInfo> UnionFind<S, P> {
    #[must_use]
    pub fn new(item_count: usize) -> Self {
        Self::new_with_initial_set_info((0..item_count).map(|_| S::default()))
    }
}

impl<S: SetInfo, P: PathInfo> UnionFind<S, P> {
    /// Create a new `UnionFind` with the given number of elements
    #[must_use]
    pub fn new_with_initial_set_info(set_infos: impl Iterator<Item = S>) -> Self {
        UnionFind {
            sets: set_infos
                .map(|set_meta| UnionFindEntry::RootOfSet { set_meta })
                .collect::<Box<[_]>>(),
            compression_lock: RwLock::new(()),
        }
    }

    /// Find an element in the `UnionFind` and return metadata about it.
    ///
    /// Panics if the item is outside the range of numbers in the union-find.
    #[must_use]
    #[expect(clippy::missing_panics_doc)]
    pub fn find(&self, item: usize) -> FindResult<'_, S, P> {
        let entry = &self.sets[item];

        match entry {
            UnionFindEntry::RootOfSet { set_meta } => FindResult {
                root_idx: item,
                set_meta,
                path_meta: None,
            },
            UnionFindEntry::OwnedBy { path_info: info, owned_by } => {
                let idx = owned_by.load(Ordering::Relaxed);

                let mut ret = self.find(idx);

                if let Some(root_meta) = ret.path_meta() {
                    let lock = self.compression_lock.write().unwrap();

                    let idx = owned_by.load(Ordering::Relaxed);

                    // It's possible that while waiting for a write lock another thread successfully compressed the branch, in which case we don't need to do anything.
                    if idx != ret.root_idx() {
                        {
                            // SAFETY: This mutable borrow is unique because
                            // - Since we are here, we know that this node has not been fully compressed yet
                            // - Therefore, `find` on this node has not been called since the last call to `union`
                            // - Therefore, there are no immutable references to this after any call to `union`
                            // - There are no immutable references from _before_ any call to `union` because `union` takes a mutable reference which would require all immutable references to disappear
                            // - There are no immutable references in other threads because the only other accesses to the data are
                            //     - While getting `idx` which is protected by a read lock,
                            //     - Here, which is protected by a write lock,
                            //     - And while setting `ret.path_meta` where that branch cannot be reached until the path compression is complete.
                            let info_mut = unsafe { &mut *info.get() };
                    
                            P::join_paths(info_mut, root_meta);
                        }

                        // Now the mutable reference is gone and it's okay for other threads to access the data. We can signal that by updating the atomic index.
                        owned_by.store(ret.root_idx(), Ordering::Relaxed);

                        // We have to drop the lock after so that any threads entering will observe the store and not perform the compression.
                        drop(lock);
                    }
                }

                ret.path_meta = Some(unsafe { &*info.get() });

                ret
            }
        }
    }

    // x = c · b
    // c^-1 · x = b

    /// Union the sets that the two representatives given belong to, with `child` becoming a child of `parent`.
    ///
    /// Panics if either `parent` or `child` are outside of the range of elements in the union-find.
    ///
    /// If `S::ALLOW_WEIGHTED` is `true`, then this will implement weighted quick union and `parent` and `child` may be swapped for performance.
    pub fn union(&mut self, parent: usize, child: usize, mut path_info: P) {
        let a_result = self.find(parent);
        let b_result = self.find(child);

        if a_result.root_idx == b_result.root_idx {
            return;
        }

        let a_idx = a_result.root_idx;
        let b_idx = b_result.root_idx;

        if let Some(b_path) = b_result.path_meta() {
            P::remove_prefix(&mut path_info, b_path);
        }

        if let Some(a_path) = a_result.path_meta() {
            P::join_paths(&mut path_info, a_path);
        }

        let old_b_data = mem::replace(
            &mut self.sets[b_idx],
            UnionFindEntry::OwnedBy { path_info: UnsafeCell::new(path_info), owned_by: AtomicUsize::new(a_idx) },
        );

        let other_set_meta = match old_b_data {
            UnionFindEntry::RootOfSet { set_meta } => set_meta,
            UnionFindEntry::OwnedBy { path_info: _, owned_by: _ } => unreachable!(),
        };

        match &mut self.sets[a_idx] {
            UnionFindEntry::RootOfSet { set_meta } => {
                set_meta.merge(other_set_meta);
            }
            UnionFindEntry::OwnedBy { path_info: _, owned_by: _ } => unreachable!(),
        }
    }
}
