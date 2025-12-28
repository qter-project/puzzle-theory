use std::{
    cell::{RefCell, UnsafeCell},
    fmt::Debug,
    marker::PhantomData,
    mem,
};

use crate::{numbers::{I, Int}, permutations::Permutation};

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

    fn remove_prefix((): &mut Self, (): &Self) {
    }
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
        inv.exponentiate(-Int::<I>::one());
        inv.compose_into(path);
        *path = inv;
    }
}

enum UnionFindEntry<S: SetInfo, P: PathInfo> {
    RootOfSet { set_meta: S },
    // Tuple of (owned by, path info)
    OwnedBy(UnsafeCell<(usize, P)>),
}

/// A data structure allowing you track disjoint sets of numbers. In puzzle-theory, this means orbits in a permutation group but you can use it for anything.
///
/// This structure also keeps track of metadata for each set and element. If you do not need this, use `()` for the `S` parameter.
pub struct UnionFind<S: SetInfo, P: PathInfo> {
    sets: Box<[UnionFindEntry<S, P>]>,
    _unsync: PhantomData<RefCell<()>>,
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
        let mut sets = Vec::with_capacity(item_count);

        for _ in 0..item_count {
            sets.push(UnionFindEntry::RootOfSet {
                set_meta: S::default(),
            });
        }

        UnionFind {
            sets: Box::from(sets),
            _unsync: PhantomData,
        }
    }
}

impl<S: SetInfo + Debug, P: PathInfo + Debug> UnionFind<S, P> {
    /// Create a new `UnionFind` with the given number of elements
    #[must_use]
    pub fn new_with_initial_set_info(set_infos: Vec<S>) -> Self {
        let mut sets = Vec::with_capacity(set_infos.len());

        for info in set_infos {
            sets.push(UnionFindEntry::RootOfSet { set_meta: info });
        }

        UnionFind {
            sets: Box::from(sets),
            _unsync: PhantomData,
        }
    }

    /// Find an element in the `UnionFind` and return metadata about it.
    ///
    /// Panics if the item is outside the range of numbers in the union-find.
    #[must_use]
    pub fn find(&self, item: usize) -> FindResult<'_, S, P> {
        let entry = &self.sets[item];

        match entry {
            UnionFindEntry::RootOfSet { set_meta } => FindResult {
                root_idx: item,
                set_meta,
                path_meta: None,
            },
            UnionFindEntry::OwnedBy(info) => {
                let mut ret = {
                    let data = unsafe { &*info.get() };
                    self.find(data.0)
                };

                if let Some(root_meta) = ret.path_meta() {
                    // SAFETY: This mutable borrow is unique because once this function returns, the node is guaranteed to be a child of a root and compression will not happen again until `union` is called. This function returns an `&` reference to the union-find and `union` takes an `&mut` reference so `union` will not be called until the reference goes away. Therefore, this branch will never get hit while an immutable reference to this is being held.
                    // Also the union-find is unsend so we can't be doing this on another thread either
                    {
                        let info_mut = unsafe { &mut *info.get() };
                        info_mut.0 = ret.root_idx;
                        P::join_paths(&mut info_mut.1, root_meta);
                    }
                }

                ret.path_meta = Some(&unsafe { &*info.get() }.1);

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
            UnionFindEntry::OwnedBy(UnsafeCell::new((a_idx, path_info))),
        );

        let other_set_meta = match old_b_data {
            UnionFindEntry::RootOfSet { set_meta } => set_meta,
            UnionFindEntry::OwnedBy(_) => unreachable!(),
        };

        match &mut self.sets[a_idx] {
            UnionFindEntry::RootOfSet { set_meta } => {
                set_meta.merge(other_set_meta);
            }
            UnionFindEntry::OwnedBy(_) => unreachable!(),
        }
    }
}
