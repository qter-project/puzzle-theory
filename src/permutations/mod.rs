use std::{
    collections::HashMap,
    hash::Hash,
    sync::{Arc, OnceLock},
};

use internment::ArcIntern;
use itertools::Itertools;

use crate::{
    numbers::{I, Int, U},
    union_find::UnionFind,
};

pub mod schreier_sims;

/// A permutation subgroup defined by a set of generators along with the color of each facelet
#[derive(Clone, Debug)]
pub struct PermutationGroup {
    facelet_colors: Vec<ArcIntern<str>>,
    generators: HashMap<ArcIntern<str>, Permutation>,
    generator_inverses: HashMap<ArcIntern<str>, ArcIntern<str>>,
    orbits: OnceLock<Arc<UnionFind<(), ()>>>,
}

impl PermutationGroup {
    /// Construct a new `PermutationGroup` from a list of facelet colors and generator permutations.
    ///
    /// # Panics
    ///
    /// This function will panic if a permutation does not include an inverse generator for each generator.
    #[must_use]
    pub fn new(
        facelet_colors: Vec<ArcIntern<str>>,
        mut generators: HashMap<ArcIntern<str>, Permutation>,
    ) -> PermutationGroup {
        assert!(!generators.is_empty());

        for generator in generators.values() {
            assert!(
                generator.facelet_count <= facelet_colors.len(),
                "{}, {}",
                generator.facelet_count,
                facelet_colors.len()
            );
        }

        for perm in generators.values_mut() {
            perm.facelet_count = facelet_colors.len();
        }

        let mut generator_inverses = HashMap::new();

        'next_item: for (name, generator) in &generators {
            let mut inverse_perm = generator.to_owned();
            inverse_perm.exponentiate(Int::from(-1));
            for (name2, generator2) in &generators {
                if generator2 == &inverse_perm {
                    generator_inverses.insert(ArcIntern::clone(name), ArcIntern::clone(name2));
                    continue 'next_item;
                }
            }

            panic!("The generator {name} does not have an inverse generator");
        }

        PermutationGroup {
            facelet_colors,
            generators,
            generator_inverses,
            orbits: OnceLock::new(),
        }
    }

    /// The number of facelets in the permutation group
    #[must_use]
    pub fn facelet_count(&self) -> usize {
        self.facelet_colors.len()
    }

    /// The colors of every facelet
    #[must_use]
    pub fn facelet_colors(&self) -> &[ArcIntern<str>] {
        &self.facelet_colors
    }

    /// The identity/solved permutation of the group
    #[must_use]
    pub fn identity(&self) -> Permutation {
        Permutation {
            // Map every value to itself
            mapping: OnceLock::from((0..self.facelet_count()).collect::<Vec<_>>()),
            cycles: OnceLock::new(),
            facelet_count: self.facelet_count(),
        }
    }

    /// Get a generator by it's name
    #[must_use]
    pub fn get_generator(&self, name: &str) -> Option<&Permutation> {
        self.generators.get(&ArcIntern::from(name))
    }

    /// Iterate over all of the generators of the permutation group
    pub fn generators(&self) -> impl Iterator<Item = (ArcIntern<str>, &Permutation)> {
        self.generators
            .iter()
            .map(|(name, perm)| (name.to_owned(), perm))
    }

    /// Compose a list of generators into an existing permutation
    ///
    /// # Errors
    ///
    /// If any of the generator names don't exist, it will compose all of the generators before it and return the name of the generator that doesn't exist as an error
    pub fn compose_generators_into<'a, T: AsRef<str>>(
        &self,
        permutation: &mut Permutation,
        generators: impl Iterator<Item = &'a T>,
    ) -> Result<(), &'a T> {
        for generator in generators {
            let Some(generator) = self.generators.get(&ArcIntern::from(generator.as_ref())) else {
                return Err(generator);
            };

            permutation.compose_into(generator);
        }

        Ok(())
    }

    /// Find the inverse of a move sequence expressed as a product of generators
    ///
    /// # Panics
    ///
    /// This function will panic if the generator moves are not all valid generators of the group
    pub fn invert_generator_moves(&self, generator_moves: &mut [ArcIntern<str>]) {
        generator_moves.reverse();

        for generator_move in generator_moves {
            *generator_move =
                ArcIntern::clone(self.generator_inverses.get(generator_move).unwrap());
        }
    }

    /// Get the orbits of all of the stickers
    pub fn orbits(&self) -> &UnionFind<(), ()> {
        self.orbits.get_or_init(|| {
            let mut union_find = UnionFind::new(self.facelet_count());

            for (_, generator) in self.generators() {
                for (from, to) in generator.mapping().all_changes() {
                    union_find.union(from, to, ());
                }
            }

            Arc::new(union_find)
        })
    }
}

/// An element of a permutation group
#[derive(Clone)]
pub struct Permutation {
    pub(crate) facelet_count: usize,
    // It is required that one of these two must be defined
    // `mapping` is also required to be minimal in the sense that there are no facelets that map to themselves at the end of the array
    mapping: OnceLock<Vec<usize>>,
    cycles: OnceLock<Vec<Vec<usize>>>,
}

impl core::fmt::Display for Permutation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let cycles = self.cycles();
        if cycles.is_empty() {
            f.write_str("Id")
        } else {
            for cycle in cycles {
                f.write_str("(")?;
                for (i, item) in cycle.iter().enumerate() {
                    write!(f, "{}{item}", if i == 0 { "" } else { ", " })?;
                }
                f.write_str(")")?;
            }
            Ok(())
        }
    }
}

impl core::fmt::Debug for Permutation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self}")
    }
}

impl Default for Permutation {
    fn default() -> Self {
        Permutation::identity()
    }
}

/// Remove useless identity mappings at the end
fn mk_minimal(mapping: &mut Vec<usize>) {
    while let Some(last) = mapping.last() && *last == mapping.len() - 1 {
        mapping.pop();
    }
}

impl Permutation {
    /// Create a permutation that represents the do-nothing permutation.
    #[must_use]
    pub fn identity() -> Permutation {
        Self::from_mapping(Vec::new())
    }

    /// Create a permutation using mapping notation. `mapping` is a list of facelet indices where the index is the facelet and the value is the facelet it permutes to.
    ///
    /// # Panics
    ///
    /// This function will panic if the mapping is not a valid permutation (i.e. if it contains duplicates or is not a complete mapping)
    #[must_use]
    pub fn from_mapping(mut mapping: Vec<usize>) -> Permutation {
        mk_minimal(&mut mapping);
        
        let facelet_count = mapping.len();

        assert!(mapping.iter().all_unique());

        Permutation {
            facelet_count,
            mapping: OnceLock::from(mapping),
            cycles: OnceLock::new(),
        }
    }

    /// Create a permutation using cycles notation. `cycles` is a list of cycles where each cycle is a list of facelet indices.
    ///
    /// # Panics
    ///
    /// This function will panic if the cycles are not a valid permutation (i.e. if it contains duplicates or is not a complete mapping)
    #[must_use]
    pub fn from_cycles(mut cycles: Vec<Vec<usize>>) -> Permutation {
        cycles.retain(|cycle| cycle.len() > 1);

        assert!(cycles.iter().flatten().all_unique());

        let facelet_count = cycles.iter().flatten().max().map_or(0, |v| v + 1);

        Permutation {
            facelet_count,
            mapping: OnceLock::new(),
            cycles: OnceLock::from(cycles),
        }
    }

    /// Get the permutation in mapping notation where `.mapping().get(facelet)` gives where the facelet permutes to
    #[expect(clippy::missing_panics_doc)]
    pub fn mapping(&self) -> Mapping<'_> {
        let mapping = self.mapping.get_or_init(|| {
            let cycles = self
                .cycles
                .get()
                .expect("either `mapping` or `cycles` to be defined");

            // Start with the identity permutation
            let mut mapping = (0..self.facelet_count).collect::<Vec<_>>();

            for cycle in cycles {
                for (&start, &end) in cycle.iter().cycle().tuple_windows().take(cycle.len()) {
                    mapping[start] = end;
                }
            }

            mapping
        });

        Mapping { mapping }
    }

    /// Get the permutation in cycles notation
    #[expect(clippy::missing_panics_doc)]
    pub fn cycles(&self) -> &[Vec<usize>] {
        self.cycles.get_or_init(|| {
            let mapping = self
                .mapping
                .get()
                .expect("either `mapping` or `cycles` to be defined");

            let mut covered = vec![false; self.facelet_count];
            let mut cycles = vec![];

            for i in 0..self.facelet_count {
                if covered[i] {
                    continue;
                }

                covered[i] = true;
                let mut cycle = vec![i];

                loop {
                    let idx = *cycle.last().unwrap();
                    let next = mapping.get(idx).copied().unwrap_or(idx);

                    if cycle[0] == next {
                        break;
                    }

                    covered[next] = true;
                    cycle.push(next);
                }

                if cycle.len() > 1 {
                    cycles.push(cycle);
                }
            }

            cycles
        })
    }

    /// Find the result of applying the permutation to the identity `power` times.
    ///
    /// This calculates the value in O(1) time with respect to `power`.
    #[allow(clippy::missing_panics_doc)]
    pub fn exponentiate(&mut self, power: Int<I>) {
        self.cycles();
        let mut mapping = self
            .mapping
            .take()
            .unwrap_or_else(|| (0..self.facelet_count).collect_vec());
        let cycles = self.cycles();

        for cycle in cycles {
            let len = Int::<U>::from(cycle.len());
            for i in 0..cycle.len() {
                mapping[cycle[i]] =
                    cycle[TryInto::<usize>::try_into((Int::<I>::from(i) + power) % len).unwrap()];
            }
        }

        mk_minimal(&mut mapping);

        self.mapping = OnceLock::from(mapping);
        self.cycles = OnceLock::new();
    }

    fn mapping_mut(&mut self) -> &mut Vec<usize> {
        self.mapping();

        self.mapping.get_mut().unwrap()
    }

    /// Compose another permutation into this permutation
    pub fn compose_into(&mut self, other: &Permutation) {
        let my_mapping = self.mapping_mut();
        let other_mapping = other.mapping();

        while my_mapping.len() < other_mapping.mapping.len() {
            my_mapping.push(my_mapping.len());
        }

        for value in my_mapping.iter_mut() {
            *value = other_mapping.get(*value);
        }

        mk_minimal(my_mapping);

        // Invalidate `cycles`
        self.cycles = OnceLock::new();
    }
}

#[derive(Clone, Copy)]
pub struct Mapping<'a> {
    mapping: &'a [usize],
}

impl<'a> Mapping<'a> {
    /// Returns where the given index maps to
    #[must_use]
    pub fn get(self, idx: usize) -> usize {
        self.mapping.get(idx).copied().unwrap_or(idx)
    }

    /// Returns an iterator over all elements of the mapping that do not map to themselves.
    pub fn all_changes(self) -> impl Iterator<Item = (usize, usize)> {
        self.mapping
            .iter()
            .copied()
            .enumerate()
            .filter(|(from, to)| from != to)
    }

    /// Get the underlying mapping as a slice. The slice is minimal in the sense that any suffix of items that are mapped to themselves are excluded.
    #[must_use] 
    pub fn minimal(self) -> &'a [usize] {
        self.mapping
    }
}

impl PartialEq for Permutation {
    fn eq(&self, other: &Self) -> bool {
        self.mapping().minimal() == other.mapping().minimal()
    }
}

impl Eq for Permutation {}

impl Hash for Permutation {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.mapping().minimal().hash(state);
    }
}

/// Represents a sequence of moves to apply to a puzzle in the `Program`
#[derive(Clone)]
pub struct Algorithm {
    perm_group: Arc<PermutationGroup>,
    permutation: Permutation,
    move_seq: Vec<ArcIntern<str>>,
    chromatic_orders: OnceLock<Vec<Int<U>>>,
    repeat: Int<U>,
}

impl Algorithm {
    /// Create an `Algorithm` instance from a move sequence
    ///
    /// # Errors
    ///
    /// If any of the moves are not valid generators of the group, it will return an error
    pub fn new_from_move_seq(
        perm_group: Arc<PermutationGroup>,
        move_seq: Vec<ArcIntern<str>>,
    ) -> Result<Algorithm, ArcIntern<str>> {
        let mut permutation = perm_group.identity();

        perm_group
            .compose_generators_into(&mut permutation, move_seq.iter())
            .map_err(ArcIntern::clone)?;

        Ok(Algorithm {
            perm_group,
            permutation,
            move_seq,
            chromatic_orders: OnceLock::new(),
            repeat: Int::<U>::one(),
        })
    }

    /// Create an `Algorithm` instance from a space separated sequence of moves
    ///
    /// # Errors
    ///
    /// If the string cannot be parsed as an algorithm, this code will return `None`
    #[must_use]
    pub fn parse_from_string(perm_group: Arc<PermutationGroup>, string: &str) -> Option<Algorithm> {
        let mut permutation = perm_group.identity();

        let mut move_seq = Vec::new();

        for moove in string.split(' ').filter(|s| !s.is_empty()) {
            let (interned, perm) = perm_group.generators().find(|v| v.0 == moove)?;

            move_seq.push(interned);
            permutation.compose_into(perm);
        }

        Some(Algorithm {
            perm_group,
            permutation,
            move_seq,
            chromatic_orders: OnceLock::new(),
            repeat: Int::<U>::one(),
        })
    }

    /// Create a new algorithm that is the identity permutation (does nothing).
    #[must_use]
    pub fn identity(perm_group: Arc<PermutationGroup>) -> Algorithm {
        let identity = perm_group.identity();
        Algorithm {
            perm_group,
            permutation: identity,
            move_seq: Vec::new(),
            chromatic_orders: OnceLock::new(),
            repeat: Int::<U>::one(),
        }
    }

    pub fn compose_into(&mut self, other: &Algorithm) {
        if self.repeat != Int::<U>::one() {
            self.move_seq = self.move_seq_iter().cloned().collect();
            self.repeat = Int::<U>::one();
        }
        self.move_seq.extend(other.move_seq_iter().cloned());
        self.permutation.compose_into(&other.permutation);
        self.chromatic_orders = OnceLock::new();
    }

    /// Get the underlying permutation of the `Algorithm` instance
    pub fn permutation(&self) -> &Permutation {
        &self.permutation
    }

    /// Find the result of applying the algorithm to the identity `exponent` times.
    ///
    /// This calculates the value in O(1) time with respect to `exponent`.
    pub fn exponentiate(&mut self, exponent: Int<I>) {
        if exponent.signum() == -1 {
            self.perm_group.invert_generator_moves(&mut self.move_seq);
        }

        self.repeat *= exponent.abs();
        self.permutation.exponentiate(exponent);
    }

    /// Returns a move sequence that when composed, give the same result as applying `.permutation()`
    pub fn move_seq_iter(&self) -> impl Iterator<Item = &ArcIntern<str>> {
        self.move_seq
            .iter()
            .cycle()
            .take(self.move_seq.len() * self.repeat.try_into().unwrap_or(usize::MAX))
    }

    /// Return the permutation group that this alg operates on
    pub fn group(&self) -> &PermutationGroup {
        &self.perm_group
    }

    /// Return the permutation group that this alg operates on in an Arc
    pub fn group_arc(&self) -> Arc<PermutationGroup> {
        Arc::clone(&self.perm_group)
    }
}

impl PartialEq for Algorithm {
    fn eq(&self, other: &Self) -> bool {
        self.move_seq_iter()
            .zip(other.move_seq_iter())
            .all(|(a, b)| a == b)
    }
}

impl Eq for Algorithm {}

impl core::fmt::Debug for Algorithm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, generator) in self.move_seq_iter().enumerate() {
            if i != 0 {
                f.write_str(" ")?;
            }
            f.write_str(generator)?;
        }

        f.write_str(" — ")?;
        self.permutation().fmt(f)
    }
}

#[cfg(test)]
mod tests {
    use internment::ArcIntern;

    use crate::{
        numbers::{I, Int},
        puzzle_geometry::parsing::puzzle,
    };

    #[test]
    fn exponentiation() {
        let cube_group = puzzle("3x3").permutation_group();

        let mut perm = cube_group.identity();

        cube_group
            .compose_generators_into(
                &mut perm,
                [ArcIntern::from("U"), ArcIntern::from("L")].iter(),
            )
            .unwrap();

        let mut exp_perm = perm.clone();
        exp_perm.exponentiate(Int::<I>::from(7_u64));

        let mut repeat_compose_perm = cube_group.identity();

        repeat_compose_perm.compose_into(&perm);
        repeat_compose_perm.compose_into(&perm);
        repeat_compose_perm.compose_into(&perm);
        repeat_compose_perm.compose_into(&perm);
        repeat_compose_perm.compose_into(&perm);
        repeat_compose_perm.compose_into(&perm);
        repeat_compose_perm.compose_into(&perm);

        assert_eq!(exp_perm, repeat_compose_perm);
    }
}
