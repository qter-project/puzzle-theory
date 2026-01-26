use std::sync::LazyLock;
use std::{collections::VecDeque, option::Option, sync::Arc};

use itertools::Itertools;

use crate::permutations::{Permutation, PermutationGroup};

use crate::numbers::{Int, U};
use crate::union_find::{Cardinality, UnionFind};

static IDENTITY: LazyLock<Permutation> = LazyLock::new(Permutation::identity);

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

    #[cfg(feature = "rand")]
    pub fn random<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> Permutation {
        self.stabilizers.random(rng)
    }
}

struct Stabilizer {
    group: Arc<PermutationGroup>,
    next: Option<Box<Stabilizer>>,
    stabilizes: usize,
    generating_set: Vec<Permutation>,
    coset_reps: UnionFind<Cardinality, Permutation>,
}

impl Stabilizer {
    fn new(group: Arc<PermutationGroup>, chain: &[usize]) -> Stabilizer {
        let (head, tail) = chain.split_first().unwrap();

        Stabilizer {
            stabilizes: *head,
            next: (!tail.is_empty()).then(|| Box::new(Stabilizer::new(Arc::clone(&group), tail))),
            coset_reps: UnionFind::new(group.facelet_count()),
            generating_set: Vec::new(),
            group,
        }
    }

    fn coset_count(&self) -> usize {
        self.coset_reps.find(self.stabilizes).set_meta().0
    }

    fn cardinality(&self) -> Int<U> {
        let mut cardinality = Int::from(self.coset_count());
        if let Some(next) = &self.next {
            cardinality *= next.cardinality();
        }
        cardinality
    }

    #[must_use]
    fn is_member(&self, mut permutation: Permutation) -> bool {
        let rep = permutation
            .mapping()
            .get(self.stabilizes);

        let find_info = self.coset_reps.find(rep);

        if find_info.root_idx() != self.stabilizes {
            return false
        }

        if let Some(perm) = find_info.path_meta() {
            permutation.compose_into(perm);
        }

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
            .get(self.stabilizes);

        let find_info = self.coset_reps.find(rep);

        if find_info.root_idx() != self.stabilizes {
            return Vec::new();
        }

        if let Some(perm) = find_info.path_meta() {
            permutation.compose_into(perm);
        }

        let other_perm = find_info.path_meta().unwrap_or_else(|| &IDENTITY);

        match &self.next {
            Some(next) => {
                let mut soln = next.solution(permutation);
                soln.push(other_perm);
                soln
            },
            None => vec![other_perm],
        }
    }

    #[cfg(feature = "rand")]
    fn random<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> Permutation {
        let mut prev = match &self.next {
            Some(next) => next.random(rng),
            None => Permutation::identity(),
        };

        let which = rng.random_range(0..self.coset_count());

        let mut count = 0;
        for i in 0..self.group.facelet_count() {
            let find_info = self.coset_reps.find(i);
            if find_info.root_idx() == self.stabilizes {
                if count == which {
                    if let Some(perm) = find_info.path_meta() {
                        prev.compose_into(perm);
                    }

                    return prev;
                }

                count += 1;
            }
        }

        panic!("Should have found a permutation")
    }

    fn inverse_rep_to(&self, rep: usize, alg: &mut Permutation) -> Result<(), ()> {
        let find_info = self.coset_reps.find(rep);

        if find_info.root_idx() != self.stabilizes {
            return Err(());
        }

        if let Some(other_alg) = find_info.path_meta() {
            alg.compose_into(other_alg);
        }

        Ok(())
    }

    fn extend(&mut self, generator: Permutation) {
        // Early quit if this new generator doesn't add anything new to the group
        if self.is_member(generator.clone()) {
            return;
        }

        self.generating_set.push(generator);
        let generator = self.generating_set.last().unwrap();

        let mapping = generator.mapping();
        let mut inv = generator.clone();
        inv.invert();

        // Find stickers that are made newly in orbit by this generator; this only does the first level of BFS
        let mut newly_in_orbit = VecDeque::new();

        for i in 0..self.group.facelet_count() {
            if self.coset_reps.find(i).root_idx() == self.stabilizes
                && self.coset_reps.find(mapping.get(i)).root_idx() != self.stabilizes
            {
                let inv_rep = inv.clone();
                self.coset_reps.union(i, mapping.get(i), inv_rep);
                newly_in_orbit.push_back(mapping.get(i));
            }
        }

        // Complete the BFS and find everything new in orbit
        while let Some(spot) = newly_in_orbit.pop_front() {
            for perm in &self.generating_set {
                let goes_to = perm.mapping().get(spot);
                if self.coset_reps.find(goes_to).root_idx() != self.stabilizes {
                    let mut inv_alg = perm.clone();
                    inv_alg.invert();
                    self.coset_reps.union(spot, goes_to, inv_alg);
                    newly_in_orbit.push_back(goes_to);
                }
            }
        }

        if self.next.is_none() {
            return;
        }

        // Sift new generators down the chain
        for i in 0..self.group.facelet_count() {
            let mut rep = Permutation::identity();
            let Ok(()) = self.inverse_rep_to(i, &mut rep) else {
                continue;
            };

            rep.invert();

            for generator in &self.generating_set {
                let mut new_generator = rep.clone();
                new_generator.compose_into(generator);
                self.inverse_rep_to(new_generator.mapping().get(self.stabilizes), &mut new_generator)
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

    #[cfg(feature = "rand")]
    #[test]
    fn random() {
        use std::collections::HashSet;

        use rand::SeedableRng;

        let cube_def = puzzle("3x3").permutation_group();
        let stabchain = StabilizerChain::new(&cube_def);
        
        let mut rng = rand::rngs::SmallRng::from_seed(*b"six seven on a merry rizzmas6767");

        let mut perms = HashSet::new();

        perms.insert(stabchain.random(&mut rng));
        perms.insert(stabchain.random(&mut rng));
        perms.insert(stabchain.random(&mut rng));
        perms.insert(stabchain.random(&mut rng));
        perms.insert(stabchain.random(&mut rng));
        perms.insert(stabchain.random(&mut rng));

        // All unique
        assert_eq!(perms.len(), 6);
    }
}
