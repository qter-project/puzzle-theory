use std::{
    collections::HashMap,
    hash::Hash,
    mem,
    str::FromStr,
    sync::{Arc, OnceLock},
};

use chumsky::{Parser, prelude::*};
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
    piece_assignments: Vec<ArcIntern<str>>,
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
        piece_assignments: Vec<ArcIntern<str>>,
        generators: HashMap<ArcIntern<str>, Permutation>,
    ) -> PermutationGroup {
        assert_eq!(facelet_colors.len(), piece_assignments.len());
        assert!(!generators.is_empty());

        for generator in generators.values() {
            assert!(
                generator.facelet_count <= facelet_colors.len(),
                "{}, {}",
                generator.facelet_count,
                facelet_colors.len()
            );
        }

        let mut generator_inverses = HashMap::new();

        'next_item: for (name, generator) in &generators {
            let mut inverse_perm = generator.to_owned();
            inverse_perm.invert();
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
            piece_assignments,
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

    /// The pieces that every facelet belongs to
    #[must_use]
    pub fn piece_assignments(&self) -> &[ArcIntern<str>] {
        &self.piece_assignments
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
                for (from, to) in generator.goes_to().all_changes() {
                    union_find.union(from, to, ());
                }
            }

            Arc::new(union_find)
        })
    }
}

/// An element of a permutation group
#[derive(Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Permutation {
    pub(crate) facelet_count: usize,
    // It is required that one of these three must be defined
    // `mapping` and `passive` are also required to be minimal in the sense that there are no facelets that map to themselves at the end of the array
    // `cycles` is required to be canonicalized in the sense that the cycles are rotated such that the smallest element is first, the cycles themselves are sorted lexicographically, and there are no cycles of length <= 2.
    #[cfg_attr(feature = "serde", serde(with = "serde_once_lock"))]
    mapping: OnceLock<Vec<usize>>,
    #[cfg_attr(feature = "serde", serde(with = "serde_once_lock"))]
    passive: OnceLock<Vec<usize>>,
    #[cfg_attr(feature = "serde", serde(with = "serde_once_lock"))]
    cycles: OnceLock<Vec<Vec<usize>>>,
}

#[cfg(feature = "serde")]
mod serde_once_lock {
    use std::sync::OnceLock;
    use serde::{Serialize, Serializer, Deserialize, Deserializer};

    pub fn serialize<T, S>(lock: &OnceLock<T>, serializer: S) -> Result<S::Ok, S::Error>
    where
        T: Serialize,
        S: Serializer,
    {
        lock.get().serialize(serializer)
    }

    pub fn deserialize<'de, T, D>(deserializer: D) -> Result<OnceLock<T>, D::Error>
    where
        T: Deserialize<'de>,
        D: Deserializer<'de>,
    {
        let value = Option::<T>::deserialize(deserializer)?;
        let lock = OnceLock::new();
        if let Some(v) = value {
            let _ = lock.set(v);
        }
        Ok(lock)
    }
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
    while let Some(last) = mapping.last()
        && *last == mapping.len() - 1
    {
        mapping.pop();
    }
}

/// Rotate each cycle such that the smallest element is first, sort the cycles lexicographically, and remove degenerate zero or one length cycles
fn canonicalize_cycles(cycles: &mut Vec<Vec<usize>>) {
    let mut i = 0;

    while i < cycles.len() {
        if cycles[i].len() < 2 {
            cycles.swap_remove(i);
        } else {
            i += 1;
        }
    }

    for cycle in &mut *cycles {
        let (i, _) = cycle.iter().enumerate().min_by_key(|(_, v)| **v).unwrap();

        cycle.rotate_left(i);
    }

    cycles.sort_unstable();
}

impl Permutation {
    /// Create a permutation that represents the do-nothing permutation.
    #[must_use]
    pub fn identity() -> Permutation {
        Self::from_mapping(Vec::new())
    }

    /// Create a permutation using _active_ mapping notation. `mapping` is a list of facelet indices where the index is the facelet and the value is the facelet it permutes to.
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
            passive: OnceLock::new(),
            cycles: OnceLock::new(),
        }
    }

    /// Create a permutation using _passive_ mapping notation. `state` shows which facelet indices would be in which positions after applying the permutation to identity.
    ///
    /// # Panics
    ///
    /// This function will panic if the mapping is not a valid permutation (i.e. if it contains duplicates or is not a complete mapping)
    #[must_use]
    pub fn from_state(mut state: Vec<usize>) -> Permutation {
        mk_minimal(&mut state);

        let facelet_count = state.len();

        assert!(state.iter().all_unique());

        Permutation {
            facelet_count,
            mapping: OnceLock::new(),
            passive: OnceLock::from(state),
            cycles: OnceLock::new(),
        }
    }

    /// Create a permutation using cycles notation. `cycles` is a list of cycles where each cycle is a list of facelet indices.
    ///
    /// # Panics
    ///
    /// This function will panic if the cycles contain duplicate numbers
    #[must_use]
    pub fn from_cycles(cycles: Vec<Vec<usize>>) -> Permutation {
        Self::try_from_cycles(cycles).unwrap()
    }

    /// Create a permutation using cycles notation. `cycles` is a list of cycles where each cycle is a list of facelet indices. This method will return `None` if the list of cycles repeats numbers.
    #[must_use]
    pub fn try_from_cycles(mut cycles: Vec<Vec<usize>>) -> Option<Permutation> {
        canonicalize_cycles(&mut cycles);

        if !cycles.iter().flatten().all_unique() {
            return None;
        }

        let facelet_count = cycles.iter().flatten().max().map_or(0, |v| v + 1);

        Some(Permutation {
            facelet_count,
            mapping: OnceLock::new(),
            passive: OnceLock::new(),
            cycles: OnceLock::from(cycles),
        })
    }

    /// Get the permutation as a mapping between stickers where `.goes_to().get(facelet)` gives where the facelet permutes to.
    ///
    /// This mapping is in _active_ notion, meaning that each element of the mapping represents where a given facelet _goes to_. In essence, this is representing the permutation as an _action_.
    #[expect(clippy::missing_panics_doc)]
    pub fn goes_to(&self) -> Mapping<'_> {
        let mapping = self.mapping.get_or_init(|| {
            if let Some(state) = self.passive.get() {
                return inv_mapping(state);
            }

            let cycles = self
                .cycles
                .get()
                .expect("`mapping`, `passive`, or `cycles` to be defined");

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

    /// Get the permutation as a mapping between stickers where `.comes_from().get(spot)` gives what facelet is in the `spot` position after applying the permutation to identity.
    ///
    /// This mapping is in _passive_ notation, meaning that each element of the mapping represents where the facelet _comes from_. In essence, this is representing the permutation as a _state_. Rubik's cubes naturally present themselves in passive notation.
    #[expect(clippy::missing_panics_doc)]
    pub fn comes_from(&self) -> Mapping<'_> {
        let mapping = self.passive.get_or_init(|| {
            if let Some(state) = self.mapping.get() {
                return inv_mapping(state);
            }

            let cycles = self
                .cycles
                .get()
                .expect("`mapping`, `passive`, or `cycles` to be defined");

            // Start with the identity permutation
            let mut mapping = (0..self.facelet_count).collect::<Vec<_>>();

            for cycle in cycles {
                for (&start, &end) in cycle.iter().cycle().tuple_windows().take(cycle.len()) {
                    mapping[end] = start;
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
            let (mapping, is_passive) = match self.mapping.get() {
                Some(v) => (v, false),
                None => (
                    self.passive
                        .get()
                        .expect("`mapping`, `passive`, or `cycles` to be defined"),
                    true,
                ),
            };
            let mapping = Mapping { mapping };

            let mut covered = vec![false; mapping.minimal().len()];
            let mut cycles = vec![];

            for i in 0..covered.len() {
                if covered[i] {
                    continue;
                }

                covered[i] = true;
                let mut cycle = vec![i];

                loop {
                    let idx = *cycle.last().unwrap();
                    let next = mapping.get(idx);

                    if cycle[0] == next {
                        break;
                    }

                    covered[next] = true;
                    cycle.push(next);
                }

                if cycle.len() > 1 {
                    if is_passive {
                        cycle.reverse();
                    }

                    cycles.push(cycle);
                }
            }

            canonicalize_cycles(&mut cycles);

            cycles
        })
    }

    pub fn invert(&mut self) {
        mem::swap(&mut self.mapping, &mut self.passive);

        if let Some(cycles) = self.cycles.get_mut() {
            for cycle in &mut *cycles {
                cycle.reverse();
            }

            canonicalize_cycles(cycles);
        }
    }

    /// Find the result of applying the permutation to the identity `power` times.
    ///
    /// This calculates the value in O(1) time with respect to `power`.
    #[expect(clippy::missing_panics_doc)]
    pub fn exponentiate(&mut self, power: Int<I>) {
        if power == Int::<I>::zero() {
            *self = Permutation::identity();
        }

        if power < Int::<I>::zero() {
            self.invert();
        }

        let power = power.abs();

        if power == Int::<U>::one() {
            return;
        }

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
        self.passive = OnceLock::new();
        self.cycles = OnceLock::new();
    }

    fn mapping_mut(&mut self) -> &mut Vec<usize> {
        self.goes_to();

        self.mapping.get_mut().unwrap()
    }

    /// Compose another permutation into this permutation
    pub fn compose_into(&mut self, other: &Permutation) {
        let my_mapping = self.mapping_mut();
        let other_mapping = other.goes_to();

        while my_mapping.len() < other_mapping.mapping.len() {
            my_mapping.push(my_mapping.len());
        }

        for value in my_mapping.iter_mut() {
            *value = other_mapping.get(*value);
        }

        mk_minimal(my_mapping);

        // Invalidate `cycles` and `passive`
        self.cycles = OnceLock::new();
        self.passive = OnceLock::new();
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
    #[expect(clippy::missing_panics_doc)]
    pub fn minimal(self) -> &'a [usize] {
        assert!(self.mapping.last().is_none_or(|v| *v != self.mapping.len()));
        self.mapping
    }

    /// An infinite iterator over the mapping
    pub fn iter_infinite(self) -> impl Iterator<Item = usize> {
        (0..).map(move |i| self.get(i))
    }
}

fn inv_mapping(mapping: &[usize]) -> Vec<usize> {
    let mut inv_mapping = vec![0; mapping.len()];

    for (i, v) in mapping.iter().copied().enumerate() {
        inv_mapping[v] = i;
    }

    inv_mapping
}

impl PartialEq for Permutation {
    fn eq(&self, other: &Self) -> bool {
        self.goes_to().minimal() == other.goes_to().minimal()
    }
}

impl Eq for Permutation {}

impl Hash for Permutation {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.goes_to().minimal().hash(state);
    }
}

fn whitespace<'src>() -> impl Parser<'src, &'src str, (), extra::Err<Rich<'src, char>>> {
    any().filter(|c: &char| c.is_whitespace()).repeated()
}

fn digit<'src>() -> impl Parser<'src, &'src str, usize, extra::Err<Rich<'src, char>>> {
    any()
        .filter(|c: &char| c.is_ascii_digit())
        .repeated()
        .collect::<String>()
        .try_map(|v, span| v.parse::<usize>().map_err(|v| Rich::custom(span, v)))
        .padded_by(whitespace())
}

fn cycle_parser<'src>() -> impl Parser<'src, &'src str, Vec<usize>, extra::Err<Rich<'src, char>>> {
    digit()
        .separated_by(just(','))
        .allow_trailing()
        .collect()
        .delimited_by(just('('), whitespace().then(just(')')))
}

fn cycles_parser<'src>()
-> impl Parser<'src, &'src str, Vec<Vec<usize>>, extra::Err<Rich<'src, char>>> {
    cycle_parser()
        .separated_by(whitespace())
        .allow_leading()
        .allow_trailing()
        .collect()
}

impl FromStr for Permutation {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match cycles_parser().parse(s).into_result() {
            Ok(cycles) => Permutation::try_from_cycles(cycles)
                .ok_or_else(|| "The cycles repeat some numbers".to_owned()),
            Err(errs) => Err(errs.into_iter().map(|v| v.to_string()).join("\n")),
        }
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
        let mut permutation = Permutation::identity();

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
        let mut permutation = Permutation::identity();

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
        let identity = Permutation::identity();
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
    use std::collections::HashMap;

    use internment::ArcIntern;

    use crate::{
        numbers::{I, Int},
        permutations::{Permutation, PermutationGroup},
        puzzle_geometry::parsing::puzzle,
    };

    #[test]
    fn internal_conversions() {
        // active -> passive
        assert_eq!(
            Permutation::from_mapping(vec![3, 0, 2, 1])
                .comes_from()
                .minimal(),
            &[1, 3, 2, 0]
        );
        // active -> cycles
        assert_eq!(
            Permutation::from_mapping(vec![3, 0, 2, 1]).cycles(),
            [vec![0, 3, 1]]
        );
        // passive -> mapping
        assert_eq!(
            Permutation::from_state(vec![1, 3, 2, 0])
                .goes_to()
                .minimal(),
            &[3, 0, 2, 1]
        );
        // passive -> cycles
        assert_eq!(
            Permutation::from_state(vec![1, 3, 2, 0]).cycles(),
            [vec![0, 3, 1]]
        );
        // cycles -> mapping
        assert_eq!(
            Permutation::from_cycles(vec![vec![0, 3, 1]])
                .goes_to()
                .minimal(),
            &[3, 0, 2, 1]
        );
        // cycles -> passive
        assert_eq!(
            Permutation::from_cycles(vec![vec![0, 3, 1]])
                .comes_from()
                .minimal(),
            &[1, 3, 2, 0]
        );
    }

    #[test]
    fn exponentiation() {
        let cube_group = puzzle("3x3").permutation_group();

        let mut perm = Permutation::identity();

        cube_group
            .compose_generators_into(
                &mut perm,
                [ArcIntern::from("U"), ArcIntern::from("L")].iter(),
            )
            .unwrap();

        let mut exp_perm = perm.clone();
        exp_perm.exponentiate(Int::<I>::from(7_u64));

        let mut repeat_compose_perm = Permutation::identity();

        repeat_compose_perm.compose_into(&perm);
        repeat_compose_perm.compose_into(&perm);
        repeat_compose_perm.compose_into(&perm);
        repeat_compose_perm.compose_into(&perm);
        repeat_compose_perm.compose_into(&perm);
        repeat_compose_perm.compose_into(&perm);
        repeat_compose_perm.compose_into(&perm);

        assert_eq!(exp_perm, repeat_compose_perm);
    }

    #[test]
    fn perm_parsing() {
        assert_eq!(
            "(1, 2) (3, 4)".parse::<Permutation>().unwrap(),
            Permutation::from_cycles(vec![vec![1, 2], vec![3, 4]])
        );

        assert_eq!(
            "(   \t 1, 2)(3, 4)    ".parse::<Permutation>().unwrap(),
            Permutation::from_cycles(vec![vec![1, 2], vec![3, 4]])
        );

        assert_eq!(
            "   (1,2)(3,4, )".parse::<Permutation>().unwrap(),
            Permutation::from_cycles(vec![vec![1, 2], vec![3, 4]])
        );

        assert_eq!(
            "   (1,2)(3,4, )".parse::<Permutation>().unwrap(),
            Permutation::from_cycles(vec![vec![1, 2], vec![3, 4]])
        );

        assert!("(,1,2)".parse::<Permutation>().is_err());
        assert!("1,2".parse::<Permutation>().is_err());
        assert!("(((1,2)".parse::<Permutation>().is_err());
        assert!("(1,2)(2,3)".parse::<Permutation>().is_err());
    }

    #[test]
    fn mk_group() {
        let mut generators = HashMap::new();

        generators.insert(ArcIntern::from("A"), "( 0  , 1 , 2,  )".parse().unwrap());
        generators.insert(ArcIntern::from("B"), "(3, 4, 5,)".parse().unwrap());
        generators.insert(ArcIntern::from("C"), "(5, 6, 7)".parse().unwrap());
        generators.insert(ArcIntern::from("D"), "(8, 9)".parse().unwrap());
        generators.insert(ArcIntern::from("E"), "(10, 11, 12, 13)".parse().unwrap());
        generators.insert(ArcIntern::from("A'"), "(2, 1, 0)".parse().unwrap());
        generators.insert(ArcIntern::from("B'"), "(5, 4, 3)".parse().unwrap());
        generators.insert(ArcIntern::from("C'"), "(7, 6, 5)".parse().unwrap());
        generators.insert(ArcIntern::from("E'"), "(13, 12, 11, 10)".parse().unwrap());

        let _ = PermutationGroup::new(
            vec![
                ArcIntern::from("A"),
                ArcIntern::from("B"),
                ArcIntern::from("C"),
                ArcIntern::from("D"),
                ArcIntern::from("E"),
                ArcIntern::from("F"),
                ArcIntern::from("G"),
                ArcIntern::from("H"),
                ArcIntern::from("I"),
                ArcIntern::from("J"),
                ArcIntern::from("K"),
                ArcIntern::from("L"),
                ArcIntern::from("K"),
                ArcIntern::from("L"),
            ],
            vec![ArcIntern::from("A"); 14],
            generators,
        );
    }
}
