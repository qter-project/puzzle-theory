use std::sync::{Arc, LazyLock};

use chumsky::{Parser, error::Rich, extra::Full, prelude::{choice, just}};
use internment::ArcIntern;

use crate::{
    puzzle_geometry::{
        PuzzleDescriptionString, PuzzleGeometry, PuzzleGeometryDefinition, knife::{CutSurface, PlaneCut},
        num::{Num, Vector}, shapes::{CUBE, DODECAHEDRON, TETRAHEDRON},
    },
    span::{File, Span, WithSpan},
};

/// Parse a puzzle definition
#[must_use] 
pub fn puzzle_definition() -> impl Parser<'static, File, WithSpan<Arc<PuzzleGeometry>>, Full<Rich<'static, char, Span>, (), ()>> {
    choice((
        just("3x3").to_span().map(|span: Span| span.with(Arc::clone(&*THREE_BY_THREE))),
        just("pyraminx").to_span().map(|span: Span| span.with(Arc::clone(&*PYRAMINX))),
        just("megaminx").to_span().map(|span: Span| span.with(Arc::clone(&*MEGAMINX))),
    ))
}

/// Get a puzzle from a static definition. Useful for testcases.
///
/// # Panics
///
/// Panics if the definition is invalid.
#[must_use]
pub fn puzzle(def: &'static str) -> WithSpan<Arc<PuzzleGeometry>> {
    puzzle_definition().parse(File::from(def)).into_output().unwrap()
}

static THREE_BY_THREE: LazyLock<Arc<PuzzleGeometry>> = LazyLock::new(|| {
    let cube = PuzzleGeometryDefinition {
        polyhedron: CUBE.to_owned(),
        cut_surfaces: vec![
            Arc::from(PlaneCut {
                spot: Vector::new_ratios([[(1, 3), (0, 1), (0, 1)]]),
                normal: Vector::new([[1, 0, 0]]),
                name: ArcIntern::from("R"),
            }),
            Arc::from(PlaneCut {
                spot: Vector::new_ratios([[(-1, 3), (0, 1), (0, 1)]]),
                normal: Vector::new([[-1, 0, 0]]),
                name: ArcIntern::from("L"),
            }),
            Arc::from(PlaneCut {
                spot: Vector::new_ratios([[(0, 1), (1, 3), (0, 1)]]),
                normal: Vector::new([[0, 1, 0]]),
                name: ArcIntern::from("U"),
            }),
            Arc::from(PlaneCut {
                spot: Vector::new_ratios([[(0, 1), (-1, 3), (0, 1)]]),
                normal: Vector::new([[0, -1, 0]]),
                name: ArcIntern::from("D"),
            }),
            Arc::from(PlaneCut {
                spot: Vector::new_ratios([[(0, 1), (0, 1), (-1, 3)]]),
                normal: Vector::new([[0, 0, -1]]),
                name: ArcIntern::from("F"),
            }),
            Arc::from(PlaneCut {
                spot: Vector::new_ratios([[(0, 1), (0, 1), (1, 3)]]),
                normal: Vector::new([[0, 0, 1]]),
                name: ArcIntern::from("B"),
            }),
        ],
        definition: Span::new(ArcIntern::from("3x3x3"), 0, 3),
    };

    Arc::new(cube.geometry().unwrap())
});

static PYRAMINX: LazyLock<Arc<PuzzleGeometry>> = LazyLock::new(|| {
        let up = TETRAHEDRON.0[0].points[0].clone().0;
        let down1 = TETRAHEDRON.0[3].points[0].clone().0;
        let down2 = TETRAHEDRON.0[3].points[1].clone().0;
        let down3 = TETRAHEDRON.0[3].points[2].clone().0;

        let pyraminx = PuzzleGeometryDefinition {
            polyhedron: TETRAHEDRON.to_owned(),
            cut_surfaces: vec![
                Arc::from(PlaneCut {
                    spot: up.clone() / &Num::from(9),
                    normal: up.clone(),
                    name: ArcIntern::from("A"),
                }),
                Arc::from(PlaneCut {
                    spot: down1.clone() / &Num::from(9),
                    normal: down1.clone(),
                    name: ArcIntern::from("B"),
                }),
                Arc::from(PlaneCut {
                    spot: down2.clone() / &Num::from(9),
                    normal: down2.clone(),
                    name: ArcIntern::from("C"),
                }),
                Arc::from(PlaneCut {
                    spot: down3.clone() / &Num::from(9),
                    normal: down3.clone(),
                    name: ArcIntern::from("D"),
                }),
                Arc::from(PlaneCut {
                    spot: (up.clone() / &Num::from(9)) * &Num::from(5),
                    normal: up.clone(),
                    name: ArcIntern::from("E"),
                }),
                Arc::from(PlaneCut {
                    spot: (down1.clone() / &Num::from(9)) * &Num::from(5),
                    normal: down1.clone(),
                    name: ArcIntern::from("F"),
                }),
                Arc::from(PlaneCut {
                    spot: (down2.clone() / &Num::from(9)) * &Num::from(5),
                    normal: down2.clone(),
                    name: ArcIntern::from("G"),
                }),
                Arc::from(PlaneCut {
                    spot: (down3.clone() / &Num::from(9)) * &Num::from(5),
                    normal: down3.clone(),
                    name: ArcIntern::from("H"),
                }),
            ],
            definition: Span::new(ArcIntern::from("pyraminx"), 0, 8),
        };

        Arc::new(pyraminx.geometry().unwrap())
});

static MEGAMINX: LazyLock<Arc<PuzzleGeometry>> = LazyLock::new(|| {
    let megaminx = PuzzleGeometryDefinition {
        polyhedron: DODECAHEDRON.clone(),
        // idk if this cut depth is right but WHO CARES HAHAHAH
        cut_surfaces: DODECAHEDRON.0.iter().map(|v| {
            let centroid = v.centroid();
        
            Arc::from(PlaneCut { spot: v.centroid() * &Num::from(8) / &Num::from(9), normal: centroid, name: ArcIntern::clone(&v.color) }) as Arc::<dyn CutSurface + 'static>
        }).collect(),
        definition: Span::new(ArcIntern::from("dodecahedron"), 0, "dodecahedron".len()),
    };

    Arc::new(megaminx.geometry().unwrap())
});

pub static PUZZLES: phf::Map<&'static str, PuzzleDescriptionString> = phf::phf_map! {
    "2x2x2" => "c f 0",
    "3x3x3" => "c f 0.333333333333333",
    "4x4x4" => "c f 0.5 f 0",
    "5x5x5" => "c f 0.6 f 0.2",
    "6x6x6" => "c f 0.666666666666667 f 0.333333333333333 f 0",
    "7x7x7" => "c f 0.714285714285714 f 0.428571428571429 f 0.142857142857143",
    "8x8x8" => "c f 0.75 f 0.5 f 0.25 f 0",
    "9x9x9" => "c f 0.777777777777778 f 0.555555555555556 f 0.333333333333333 f 0.111111111111111",
    "10x10x10" => "c f 0.8 f 0.6 f 0.4 f 0.2 f 0",
    "11x11x11" => "c f 0.818181818181818 f 0.636363636363636 f 0.454545454545455 f 0.272727272727273 f 0.0909090909090909",
    "12x12x12" => "c f 0.833333333333333 f 0.666666666666667 f 0.5 f 0.333333333333333 f 0.166666666666667 f 0",
    "13x13x13" => "c f 0.846153846153846 f 0.692307692307692 f 0.538461538461538 f 0.384615384615385 f 0.230769230769231 f 0.0769230769230769",
    "20x20x20" => "c f 0 f .1 f .2 f .3 f .4 f .5 f .6 f .7 f .8 f .9",
    "30x30x30" => "c f 0 f .066667 f .133333 f .2 f .266667 f .333333 f .4 f .466667 f .533333 f .6 f .666667 f .733333 f .8 f .866667 f .933333",
    "40x40x40" => "c f 0 f .05 f .1 f .15 f .2 f .25 f .3 f .35 f .4 f .45 f .5 f .55 f .6 f .65 f .7 f .75 f .8 f .85 f .9 f .95",
    "skewb" => "c v 0",
    "master skewb" => "c v 0.275",
    "professor skewb" => "c v 0 v 0.38",
    "compy cube" => "c v 0.915641442663986",
    "helicopter" => "c e 0.707106781186547",
    "curvy copter" => "c e 0.83",
    "dino" => "c v 0.577350269189626",
    "little chop" => "c e 0",
    "pyramorphix" => "t e 0",
    "mastermorphix" => "t e 0.346184634065199",
    "pyraminx" => "t v 0.333333333333333 v 1.66666666666667",
    "tetraminx" => "t v 0.333333333333333",
    "master pyraminx" => "t v 0 v 1 v 2",
    "master tetraminx" => "t v 0 v 1",
    "professor pyraminx" => "t v -0.2 v 0.6 v 1.4 v 2.2",
    "professor tetraminx" => "t v -0.2 v 0.6 v 1.4",
    "royal pyraminx" => "t v -0.333333333333333 v 0.333333333333333 v 1 v 1.66666666666667 v 2.33333333333333",
    "royal tetraminx" => "t v -0.333333333333333 v 0.333333333333333 v 1 v 1.66666666666667",
    "emperor pyraminx" => "t v -0.428571428571429 v 0.142857142857143 v 0.714285714285714 v 1.28571428571429 v 1.85714285714286 v 2.42857142857143",
    "emperor tetraminx" => "t v -0.428571428571429 v 0.142857142857143 v 0.714285714285714 v 1.28571428571429 v 1.85714285714286",
    "Jing pyraminx" => "t f 0",
    "master pyramorphix" => "t e 0.866025403784437",
    "megaminx" => "d f 0.7",
    "gigaminx" => "d f 0.64 f 0.82",
    "teraminx" => "d f 0.64 f 0.76 f 0.88",
    "petaminx" => "d f 0.64 f 0.73 f 0.82 f 0.91",
    "examinx" => "d f 0.64 f 0.712 f 0.784 f 0.856 f 0.928",
    "zetaminx" => "d f 0.64 f 0.7 f 0.76 f 0.82 f 0.88 f 0.94",
    "yottaminx" => "d f 0.64 f 0.6914 f 0.7429 f 0.7943 f 0.8457 f 0.8971 f 0.9486",
    "pentultimate" => "d f 0",
    "master pentultimate" => "d f 0.1",
    "elite pentultimate" => "d f 0 f 0.145905",
    "starminx" => "d v 0.937962370425399", // sqrt(5(5-2 sqrt(5))/3)
    "starminx 2" => "d f 0.23606797749979",
    "pyraminx crystal" => "d f 0.447213595499989",
    "chopasaurus" => "d v 0",
    "big chop" => "d e 0",
    "skewb diamond" => "o f 0",
    "FTO" => "o f 0.333333333333333",
    "master FTO" => "o f 0.5 f 0",
    "Christopher's jewel" => "o v 0.577350269189626",
    "octastar" => "o e 0",
    "Trajber's octahedron" => "o v 0.433012701892219",
    "radio chop" => "i f 0",
    "icosamate" => "i v 0",
    "Regular Astrominx" => "i v 0.18759247376021",
    "Regular Astrominx + Big Chop" => "i v 0.18759247376021 e 0",
    "Redicosahedron" => "i v 0.794654472291766",
    "Redicosahedron with centers" => "i v 0.84",
    "Icosaminx" => "i v 0.73",
    "Eitan's star" => "i f 0.61803398874989",
    "2x2x2 + dino" => "c f 0 v 0.577350269189626",
    "2x2x2 + little chop" => "c f 0 e 0",
    "dino + little chop" => "c v 0.577350269189626 e 0",
    "2x2x2 + dino + little chop" => "c f 0 v 0.577350269189626 e 0",
    "megaminx + chopasaurus" => "d f 0.61803398875 v 0",
    "starminx combo" => "d f 0.23606797749979 v 0.937962370425399",
};
