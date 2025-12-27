use std::{collections::VecDeque, option::Option, sync::Arc};

use itertools::Itertools;

use crate::permutations::{Permutation, PermutationGroup};

use crate::numbers::{I, Int, U};

pub struct StabilizerChain {
    stabilizers: Stabilizer,
}

impl StabilizerChain {
    /// Create a new stabilizer chain from the permutation group using the Schreier-Sims algorithm.
    #[must_use]
    pub fn new(group: &Arc<PermutationGroup>) -> StabilizerChain {
        Self::new_with_chain(group, &(0..group.facelet_count()).collect_vec())
    }

    /// Create a new stabilizer chain from the permutation group with the stickers being stabilized in the given order. It is a logic error for any stickers to be left out of the chain or duplicated.
    ///
    /// # Panics
    ///
    /// Panics if any elements of `chain` are out of range for the size of the permutation group.
    #[must_use] 
    pub fn new_with_chain(group: &Arc<PermutationGroup>, chain: &[usize]) -> StabilizerChain {
        let mut stabilizers = Stabilizer::new(Arc::clone(group), chain);

        for (_, perm) in group.generators() {
            stabilizers.extend(perm.to_owned());
        }

        StabilizerChain { stabilizers }
    }

    /// Determine if a permutation is a member of the group
    #[must_use]
    pub fn is_member(&self, permutation: Permutation) -> bool {
        self.stabilizers.is_member(permutation)
    }

    /// Calculate the cardinality of the group
    #[must_use]
    pub fn cardinality(&self) -> Int<U> {
        self.stabilizers.cardinality()
    }

    /// Return the sequence of inverse coset representatives from each stabilizer in the chain that when composed together, inverts the permutation. If the input is not a member of the group, the sequence will be cut short once the algorithm can recognize that.
    #[must_use]
    pub fn solution(&self, permutation: Permutation) -> Vec<&Permutation> {
        let mut soln = self.stabilizers.solution(permutation);
        soln.reverse();
        soln
    }
}

#[derive(Debug)]
struct Stabilizer {
    group: Arc<PermutationGroup>,
    next: Option<Box<Stabilizer>>,
    stabilizes: usize,
    generating_set: Vec<Permutation>,
    coset_reps: Box<[Option<Permutation>]>,
}

impl Stabilizer {
    fn new(group: Arc<PermutationGroup>, chain: &[usize]) -> Stabilizer {
        let (head, tail) = chain.split_first().unwrap();

        let mut coset_reps = Box::<[_]>::from(vec![None; group.facelet_count()]);
        coset_reps[*head] = Some(group.identity());

        Stabilizer {
            stabilizes: *head,
            next: (!tail.is_empty()).then(|| Box::new(Stabilizer::new(Arc::clone(&group), tail))),
            coset_reps,
            generating_set: Vec::new(),
            group,
        }
    }

    fn cardinality(&self) -> Int<U> {
        let mut cardinality = Int::from(self.coset_reps.iter().filter(|v| v.is_some()).count());
        if let Some(next) = &self.next {
            cardinality *= next.cardinality();
        }
        cardinality
    }

    #[must_use]
    fn is_member(&self, mut permutation: Permutation) -> bool {
        let rep = permutation
            .mapping()
            .get(self.stabilizes)
            .copied()
            .unwrap_or(self.stabilizes);

        let Some(other_perm) = &self.coset_reps[rep] else {
            return false;
        };

        permutation.compose_into(other_perm);

        match &self.next {
            Some(next) => next.is_member(permutation),
            None => true,
        }
    }

    /// Returns the solution backwards for efficiency
    #[must_use]
    fn solution(&self, mut permutation: Permutation) -> Vec<&Permutation> {
        let rep = permutation
            .mapping()
            .get(self.stabilizes)
            .copied()
            .unwrap_or(self.stabilizes);

        let Some(other_perm) = &self.coset_reps[rep] else {
            return Vec::new();
        };

        permutation.compose_into(other_perm);

        match &self.next {
            Some(next) => {
                let mut soln = next.solution(permutation);
                soln.push(other_perm);
                soln
            },
            None => vec![other_perm],
        }
    }

    fn inverse_rep_to(&self, rep: usize, alg: &mut Permutation) -> Result<(), ()> {
        let Some(other_alg) = &self.coset_reps[rep] else {
            return Err(());
        };

        alg.compose_into(other_alg);

        Ok(())
    }

    fn extend(&mut self, generator: Permutation) {
        // Early quit if this new generator doesn't add anything new to the group
        if self.is_member(generator.clone()) {
            return;
        }

        self.generating_set.push(generator);
        let generator = self.generating_set.last().unwrap();

        let mapping = generator.mapping().to_owned();
        let mut inv = generator.clone();
        inv.exponentiate(-Int::<I>::one());

        // Find stickers that are made newly in orbit by this generator; this only does the first level of BFS
        let mut newly_in_orbit = VecDeque::new();

        for i in 0..self.coset_reps.len() {
            if let Some(prev_inv_rep) = &self.coset_reps[i]
                && self.coset_reps[mapping.get(i).copied().unwrap_or(i)].is_none()
            {
                let mut inv_rep = inv.clone();
                inv_rep.compose_into(prev_inv_rep);
                self.coset_reps[mapping[i]] = Some(inv_rep);
                newly_in_orbit.push_back(mapping[i]);
            }
        }

        // Complete the BFS and find everything new in orbit
        while let Some(spot) = newly_in_orbit.pop_front() {
            for perm in &self.generating_set {
                let goes_to = perm.mapping().get(spot).copied().unwrap_or(spot);
                if self.coset_reps[goes_to].is_none() {
                    let mut inv_alg = perm.clone();
                    inv_alg.exponentiate(-Int::<I>::one());
                    inv_alg.compose_into(self.coset_reps[spot].as_ref().unwrap());
                    self.coset_reps[goes_to] = Some(inv_alg);
                    newly_in_orbit.push_back(goes_to);
                }
            }
        }

        if self.next.is_none() {
            return;
        }

        // Sift new generators down the chain
        for i in 0..self.coset_reps.len() {
            let mut rep = self.group.identity();
            let Ok(()) = self.inverse_rep_to(i, &mut rep) else {
                continue;
            };

            rep.exponentiate(-Int::<I>::one());

            for generator in &self.generating_set {
                let mut new_generator = rep.clone();
                new_generator.compose_into(generator);
                self.inverse_rep_to(new_generator.mapping()[self.stabilizes], &mut new_generator)
                    .unwrap();
                self.next.as_mut().unwrap().extend(new_generator);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::HashMap, sync::Arc};

    use internment::ArcIntern;

    use crate::{
        numbers::{Int, U},
        permutations::{Algorithm, Permutation, PermutationGroup},
        puzzle_geometry::parsing::puzzle,
    };

    use super::StabilizerChain;

    #[test]
    fn simple() {
        let mut perms = HashMap::new();
        perms.insert(
            ArcIntern::from("A"),
            Permutation::from_cycles(vec![vec![0, 1, 2]]),
        );
        perms.insert(
            ArcIntern::from("B"),
            Permutation::from_cycles(vec![vec![0, 2, 1]]),
        );

        let puzzle = Arc::new(PermutationGroup::new(
            vec![
                ArcIntern::from("a"),
                ArcIntern::from("b"),
                ArcIntern::from("c"),
            ],
            perms,
        ));

        let method = StabilizerChain::new(&puzzle);
        assert_eq!(method.cardinality(), Int::<U>::from(3_u32));
        assert!(!method.is_member(Permutation::from_cycles(vec![vec![0, 1]])));
        assert!(method.is_member(Permutation::from_cycles(vec![vec![0, 1, 2]])));
    }

    #[test]
    fn three_by_three() {
        let cube_def = puzzle("3x3").permutation_group();

        let method = StabilizerChain::new(&cube_def);

        assert_eq!(
            method.cardinality(),
            "43252003274489856000".parse::<Int<U>>().unwrap()
        );

        // Corner twist
        assert!(!method.is_member(Permutation::from_cycles(vec![vec![10, 16, 5]])));

        // U alg
        assert!(
            method.is_member(
                Algorithm::new_from_move_seq(Arc::clone(&cube_def), vec![ArcIntern::from("U")])
                    .unwrap()
                    .permutation()
                    .clone()
            )
        );

        // Sexy move
        assert!(
            method.is_member(
                Algorithm::new_from_move_seq(
                    Arc::clone(&cube_def),
                    vec![
                        ArcIntern::from("U"),
                        ArcIntern::from("R"),
                        ArcIntern::from("U'"),
                        ArcIntern::from("R'"),
                    ]
                )
                .unwrap()
                .permutation()
                .clone()
            )
        );

        // Two corner twists to make the orientation sum work
        assert!(method.is_member(Permutation::from_cycles(vec![
            vec![10, 16, 5],
            vec![18, 7, 24]
        ])));
    }
}
