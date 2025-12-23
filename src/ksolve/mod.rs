use std::num::{NonZeroU8, NonZeroU16};
use thiserror::Error;

/// A representation of a puzzle in the `KSolve` format. We choose to remain
/// consistent with `KSolve` format and terminology because it is the
/// lingua-franca of the puzzle theory community. twsearch, another popular
/// puzzle software suite, also uses the `KSolve` format.
#[derive(Clone, Debug, PartialEq)]
pub struct KSolve {
    pub(crate) name: String,
    pub(crate) sets: Vec<KSolveSet>,
    pub(crate) moves: Vec<KSolveMove>,
    pub(crate) symmetries: Vec<KSolveMove>,
}

/// A piece orbit of a `KSolve` puzzle, or "Set" to remain consistent with the
/// `KSolve` terminology
#[derive(Clone, Debug, PartialEq)]
pub struct KSolveSet {
    pub(crate) name: String,
    pub(crate) piece_count: NonZeroU16,
    pub(crate) orientation_count: NonZeroU8,
}

/// A transformation of a `KSolve` puzzle. A list of (permutation vector,
/// orientation vector)
pub type KSolveTransformation = Vec<Vec<(NonZeroU16, u8)>>;

#[derive(Clone, Debug, PartialEq)]
pub struct KSolveMove {
    pub(crate) transformation: KSolveTransformation,
    pub(crate) name: String,
}

impl KSolve {
    /// Get the name of the puzzle
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Get the sets of pieces on the puzzle
    #[must_use]
    pub fn sets(&self) -> &[KSolveSet] {
        &self.sets
    }

    /// Get the set of available moves on the puzzle
    #[must_use]
    pub fn moves(&self) -> &[KSolveMove] {
        &self.moves
    }

    /// Get the list of symmetries obeyed by the puzzle
    // TODO: how should reflection symmetries be represented?
    #[must_use]
    pub fn symmetries(&self) -> &[KSolveMove] {
        &self.symmetries
    }

    /// Get the solved state of the puzzle
    #[must_use]
    // Should not panic
    #[allow(clippy::missing_panics_doc)]
    pub fn solved(&self) -> KSolveTransformation {
        self.sets
            .iter()
            .map(|ksolve_set| {
                (1..=ksolve_set.piece_count.get())
                    .map(|i| i.try_into().unwrap())
                    .zip(std::iter::repeat(0))
                    .collect()
            })
            .collect()
    }

    #[must_use]
    pub fn with_moves(self, moves: &[&str]) -> Self {
        let moves = self
            .moves
            .into_iter()
            .filter(|m| moves.contains(&m.name.as_str()))
            .collect();
        Self {
            name: self.name,
            sets: self.sets,
            moves,
            symmetries: self.symmetries,
        }
    }
}

impl KSolveSet {
    /// Get the name of the set
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Get the number of pieces in the set
    #[must_use]
    pub fn piece_count(&self) -> NonZeroU16 {
        self.piece_count
    }

    /// Get the orientation modulo of the set
    #[must_use]
    pub fn orientation_count(&self) -> NonZeroU8 {
        self.orientation_count
    }
}

impl KSolveMove {
    /// Get the name of the move
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Get the transformation of the move
    #[must_use]
    pub fn transformation(&self) -> &KSolveTransformation {
        &self.transformation
    }

    /// Convenience method for converting `KSolve`'s 1-indexed permutation vectors
    /// to 0-indexed permutation vectors
    #[must_use]
    pub fn zero_indexed_transformation(&self) -> Vec<Vec<(u16, u8)>> {
        self.transformation
            .iter()
            .map(|perm_and_ori| {
                perm_and_ori
                    .iter()
                    .map(|&(p, o)| (p.get() - 1, o))
                    .collect()
            })
            .collect()
    }
}

/// A possibly invalid `KSolve` puzzle representation
pub(crate) struct KSolveFields {
    name: String,
    sets: Vec<KSolveSet>,
    moves: Vec<KSolveMove>,
    symmetries: Vec<KSolveMove>,
}

#[derive(Error, Debug)]
pub enum KSolveConstructionError {
    #[error("Invalid set count, expected {0} sets but got {1}")]
    InvalidSetCount(usize, usize),
    #[error("Invalid piece count, expected {0} pieces but got {1}")]
    InvalidPieceCount(u16, usize),
    #[error("Invalid orientation delta, expected a value between 0 and {0} but got {1}")]
    InvalidOrientationDelta(u8, u8),
    #[error("Permutation out of range, expected a value between 1 and {0} but got {1}")]
    PermutationOutOfRange(u16, u16),
    #[error("Move is invalid: {0:?}")]
    InvalidMove(KSolveMove),
}

impl TryFrom<KSolveFields> for KSolve {
    type Error = KSolveConstructionError;

    fn try_from(ksolve_fields: KSolveFields) -> Result<Self, Self::Error> {
        let expected_set_count = ksolve_fields.sets.len();

        for ksolve_move in &ksolve_fields.moves {
            let actual_set_count = ksolve_move.transformation().len();

            if actual_set_count != expected_set_count {
                return Err(KSolveConstructionError::InvalidSetCount(
                    expected_set_count,
                    actual_set_count,
                ));
            }

            for (transformation, orbit_def) in
                ksolve_move.transformation.iter().zip(&ksolve_fields.sets)
            {
                let expected_piece_count = orbit_def.piece_count.get();
                let actual_piece_count = transformation.len();

                if actual_piece_count != expected_piece_count as usize {
                    return Err(KSolveConstructionError::InvalidPieceCount(
                        expected_piece_count,
                        actual_piece_count,
                    ));
                }

                let max_orientation_delta = orbit_def.orientation_count.get() - 1;
                let mut covered_perms = vec![false; expected_piece_count as usize];

                for &(perm, orientation_delta) in transformation {
                    if orientation_delta > max_orientation_delta {
                        return Err(KSolveConstructionError::InvalidOrientationDelta(
                            max_orientation_delta,
                            orientation_delta,
                        ));
                    }

                    match covered_perms.get_mut((perm.get() - 1) as usize) {
                        Some(i) => *i = true,
                        None => {
                            return Err(KSolveConstructionError::PermutationOutOfRange(
                                expected_piece_count,
                                perm.get(),
                            ));
                        }
                    }
                }

                if covered_perms.iter().any(|&x| !x) {
                    return Err(KSolveConstructionError::InvalidMove(ksolve_move.clone()));
                }
            }
        }

        Ok(KSolve {
            name: ksolve_fields.name,
            sets: ksolve_fields.sets,
            moves: ksolve_fields.moves,
            symmetries: ksolve_fields.symmetries,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::puzzle_geometry::parsing::puzzle;

    use super::*;

    #[allow(clippy::needless_pass_by_value)]
    fn nonzero_perm(transformation: Vec<Vec<(u16, u8)>>) -> KSolveTransformation {
        transformation
            .iter()
            .map(|perm_and_ori| {
                perm_and_ori
                    .iter()
                    .map(|&(p, o)| (p.try_into().unwrap(), o))
                    .collect()
            })
            .collect()
    }

    #[test]
    #[should_panic(expected = "called `Result::unwrap()` on an `Err` value: TryFromIntError(())")]
    fn test_nonzero_perm() {
        nonzero_perm(vec![
            vec![(0, 0), (2, 0), (3, 0)],
            vec![(1, 0), (2, 0), (3, 0), (4, 0)],
        ]);
    }

    #[test]
    fn test_solved_3x3() {
        let kpuzzle_3x3 = puzzle("3x3").ksolve();
        let solved = kpuzzle_3x3.solved();

        let corner_idx = usize::from(kpuzzle_3x3.sets()[0].piece_count().get() != 8);
        let edge_idx = 1 - corner_idx;

        assert_eq!(solved.len(), 2);

        let expected_edges = &(1..=12)
            .map(|i| i.try_into().unwrap())
            .zip(std::iter::repeat(0))
            .collect::<Vec<(NonZeroU16, u8)>>();
        let actual_edges = &solved[edge_idx];

        assert_eq!(expected_edges, actual_edges);

        let expected_corners = &(1..=8)
            .map(|i| i.try_into().unwrap())
            .zip(std::iter::repeat(0))
            .collect::<Vec<(NonZeroU16, u8)>>();
        let actual_corners = &solved[corner_idx];

        assert_eq!(expected_corners, actual_corners);
    }

    #[test]
    fn test_zero_indexed_transformation() {
        let kpuzzle_3x3 = puzzle("3x3").ksolve();
        let ksolve_move = &kpuzzle_3x3.moves[0];

        let expected_zero_indexed_transformation = ksolve_move
            .transformation()
            .iter()
            .map(|perm_and_ori| {
                perm_and_ori
                    .iter()
                    .map(|&(p, o)| (p.get() - 1, o))
                    .collect::<Vec<(u16, u8)>>()
            })
            .collect::<Vec<_>>();
        let actual_zero_indexed_transformation = ksolve_move.zero_indexed_transformation();

        assert_eq!(
            expected_zero_indexed_transformation,
            actual_zero_indexed_transformation
        );
    }

    #[test]
    fn test_valid_construction() {
        let ksolve_fields = KSolveFields {
            name: "hasta".to_owned(),
            sets: vec![
                KSolveSet {
                    name: "la vista".to_owned(),
                    piece_count: 3.try_into().unwrap(),
                    orientation_count: 5.try_into().unwrap(),
                },
                KSolveSet {
                    name: "baby".to_owned(),
                    piece_count: 4.try_into().unwrap(),
                    orientation_count: 5.try_into().unwrap(),
                },
            ],
            moves: vec![KSolveMove {
                name: "F".to_owned(),
                transformation: nonzero_perm(vec![
                    vec![(1, 0), (2, 0), (3, 0)],
                    vec![(1, 0), (2, 0), (3, 0), (4, 0)],
                ]),
            }],
            symmetries: vec![],
        };

        let ksolve = KSolve::try_from(ksolve_fields).unwrap();
        let expected = KSolve {
            name: "hasta".to_owned(),
            sets: vec![
                KSolveSet {
                    name: "la vista".to_string(),
                    piece_count: 3.try_into().unwrap(),
                    orientation_count: 5.try_into().unwrap(),
                },
                KSolveSet {
                    name: "baby".to_string(),
                    piece_count: 4.try_into().unwrap(),
                    orientation_count: 5.try_into().unwrap(),
                },
            ],
            moves: vec![KSolveMove {
                name: "F".to_string(),
                transformation: nonzero_perm(vec![
                    vec![(1, 0), (2, 0), (3, 0)],
                    vec![(1, 0), (2, 0), (3, 0), (4, 0)],
                ]),
            }],
            symmetries: vec![],
        };

        assert_eq!(ksolve, expected);
    }

    #[test]
    fn test_invalid_set_count() {
        let ksolve_fields = KSolveFields {
            name: "ya".to_owned(),
            sets: vec![
                KSolveSet {
                    name: "like".to_owned(),
                    piece_count: 3.try_into().unwrap(),
                    orientation_count: 5.try_into().unwrap(),
                },
                KSolveSet {
                    name: "jazz".to_owned(),
                    piece_count: 4.try_into().unwrap(),
                    orientation_count: 5.try_into().unwrap(),
                },
            ],
            moves: vec![KSolveMove {
                name: "F".to_owned(),
                transformation: nonzero_perm(vec![vec![(1, 0), (2, 0), (3, 0)]]),
            }],
            symmetries: vec![],
        };

        assert!(matches!(
            KSolve::try_from(ksolve_fields),
            Err(KSolveConstructionError::InvalidSetCount(2, 1))
        ));
    }

    #[test]
    fn test_invalid_piece_count() {
        let ksolve_fields = KSolveFields {
            name: "chat is this rizz".to_owned(),
            sets: vec![
                KSolveSet {
                    name: "john".to_owned(),
                    piece_count: 3.try_into().unwrap(),
                    orientation_count: 5.try_into().unwrap(),
                },
                KSolveSet {
                    name: "cena".to_owned(),
                    piece_count: 4.try_into().unwrap(),
                    orientation_count: 5.try_into().unwrap(),
                },
            ],
            moves: vec![KSolveMove {
                name: "F".to_owned(),
                transformation: nonzero_perm(vec![vec![(1, 0), (2, 0), (3, 0), (4, 0)], vec![]]),
            }],
            symmetries: vec![],
        };

        assert!(matches!(
            KSolve::try_from(ksolve_fields),
            Err(KSolveConstructionError::InvalidPieceCount(3, 4))
        ));
    }

    #[test]
    fn test_invalid_orientation_delta() {
        let ksolve_fields = KSolveFields {
            name: "canttouchthis".to_owned(),
            sets: vec![
                KSolveSet {
                    name: "angry".to_owned(),
                    piece_count: 3.try_into().unwrap(),
                    orientation_count: 5.try_into().unwrap(),
                },
                KSolveSet {
                    name: "birds".to_owned(),
                    piece_count: 4.try_into().unwrap(),
                    orientation_count: 5.try_into().unwrap(),
                },
            ],
            moves: vec![KSolveMove {
                name: "F".to_owned(),
                transformation: nonzero_perm(vec![
                    vec![(1, 0), (2, 0), (3, 0)],
                    vec![(1, 0), (2, 5), (3, 0), (4, 0)],
                ]),
            }],
            symmetries: vec![],
        };

        assert!(matches!(
            KSolve::try_from(ksolve_fields),
            Err(KSolveConstructionError::InvalidOrientationDelta(4, 5))
        ));
    }

    #[test]
    fn test_permutation_out_of_range() {
        let ksolve_fields = KSolveFields {
            name: "fish fight".to_owned(),
            sets: vec![
                KSolveSet {
                    name: "<><".to_owned(),
                    piece_count: 3.try_into().unwrap(),
                    orientation_count: 5.try_into().unwrap(),
                },
                KSolveSet {
                    name: "><>".to_owned(),
                    piece_count: 4.try_into().unwrap(),
                    orientation_count: 5.try_into().unwrap(),
                },
            ],
            moves: vec![KSolveMove {
                name: "F".to_owned(),
                transformation: nonzero_perm(vec![
                    vec![(1, 0), (2, 0), (3, 0)],
                    vec![(1, 0), (5, 0), (3, 0), (4, 0)],
                ]),
            }],
            symmetries: vec![],
        };

        assert!(matches!(
            KSolve::try_from(ksolve_fields),
            Err(KSolveConstructionError::PermutationOutOfRange(4, 5))
        ));
    }

    #[test]
    fn test_invalid_move() {
        let ksolve_fields = KSolveFields {
            name: "are you beginning".to_owned(),
            sets: vec![
                KSolveSet {
                    name: "to feel like".to_owned(),
                    piece_count: 3.try_into().unwrap(),
                    orientation_count: 5.try_into().unwrap(),
                },
                KSolveSet {
                    name: "a rap god".to_owned(),
                    piece_count: 4.try_into().unwrap(),
                    orientation_count: 5.try_into().unwrap(),
                },
            ],
            moves: vec![KSolveMove {
                name: "F".to_owned(),
                transformation: nonzero_perm(vec![
                    vec![(1, 0), (2, 0), (3, 0)],
                    vec![(1, 0), (2, 0), (2, 0), (4, 0)],
                ]),
            }],
            symmetries: vec![],
        };

        assert!(matches!(
            KSolve::try_from(ksolve_fields),
            Err(KSolveConstructionError::InvalidMove(_))
        ));
    }
}
