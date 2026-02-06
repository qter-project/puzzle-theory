#![allow(clippy::type_complexity)]

use std::{collections::HashMap, fmt::Display, sync::Arc};

use chumsky::Parser;
use internment::ArcIntern;
use serde::{Deserialize, Serialize};

use crate::{
    permutations::{Permutation, PermutationGroup},
    puzzle_geometry::parsing::puzzle_definition,
    span::File,
};

impl From<Permutation> for String {
    fn from(value: Permutation) -> Self {
        value.to_string()
    }
}

impl TryFrom<String> for Permutation {
    type Error = String;

    fn try_from(value: String) -> Result<Self, Self::Error> {
        value.parse()
    }
}

impl Serialize for PermutationGroup {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        if let Some(def) = &self.maybe_def {
            return serializer.serialize_str(def);
        }

        let data = (
            &self.facelet_colors,
            &self.piece_assignments,
            &self.generators,
        );

        data.serialize(serializer)
    }
}

#[derive(Deserialize)]
#[serde(untagged)]
pub enum DecodedPermGroup {
    Def(ArcIntern<str>),
    Args(
        (
            Vec<ArcIntern<str>>,
            Vec<ArcIntern<str>>,
            HashMap<ArcIntern<str>, Permutation>,
        ),
    ),
}

pub struct PuzzleDefErr(ArcIntern<str>);

impl Display for PuzzleDefErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Failed to parse puzzle definition `{}`", self.0)
    }
}

impl TryFrom<DecodedPermGroup> for PermutationGroup {
    type Error = PuzzleDefErr;

    fn try_from(value: DecodedPermGroup) -> Result<Self, Self::Error> {
        match value {
            DecodedPermGroup::Def(def) => {
                let group = {
                    let def = puzzle_definition()
                        .parse(File::new(
                            ArcIntern::from("<static>"),
                            ArcIntern::clone(&def),
                        ))
                        .into_output()
                        .ok_or(PuzzleDefErr(def))?;
                    
                    def.permutation_group()
                };

                Ok(Arc::into_inner(group).unwrap())
            },
            DecodedPermGroup::Args((facelet_colors, piece_assignments, generators)) => {
                Ok(PermutationGroup::new(facelet_colors, piece_assignments, generators))
            }
        }
    }
}
