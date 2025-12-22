use crate::puzzle_geometry::num::rotation_about;

use super::{
    Face, Point, Polyhedron, exact_trig::rotation_degree, num::{Matrix, Num, Vector, rotate_to}, 
};
use internment::ArcIntern;
use std::sync::LazyLock;

pub static TETRAHEDRON: LazyLock<Polyhedron> = LazyLock::new(|| {
    let scale = Num::from(3).sqrt();
    // Each of these points has magnitude 3 which aligns with how twizzle works
    let mut up = Point(Vector::new([[1, 1, 1]]) * &scale);
    let mut down_1 = Point(Vector::new([[1, -1, -1]]) * &scale);
    let mut down_2 = Point(Vector::new([[-1, 1, -1]]) * &scale);
    let mut down_3 = Point(Vector::new([[-1, -1, 1]]) * &scale);

    let rotate_to = rotate_to(
        Matrix::new([[1, 1, 1], [1, -1, -1]]),
        Matrix::new([[0, 1, 0], [0, 0, 1]]),
    );

    up.0 = &rotate_to * &up.0;
    down_1.0 = &rotate_to * &down_1.0;
    down_2.0 = &rotate_to * &down_2.0;
    down_3.0 = &rotate_to * &down_3.0;

    Polyhedron(vec![
        Face {
            points: vec![up.clone(), down_1.clone(), down_2.clone()],
            color: ArcIntern::from("green"),
        },
        Face {
            points: vec![up.clone(), down_2.clone(), down_3.clone()],
            color: ArcIntern::from("blue"),
        },
        Face {
            points: vec![up, down_3.clone(), down_1.clone()],
            color: ArcIntern::from("yellow"),
        },
        Face {
            points: vec![down_1, down_2, down_3],
            color: ArcIntern::from("red"),
        },
    ])
});

pub static CUBE: LazyLock<Polyhedron> = LazyLock::new(|| {
    let up = Face {
        points: vec![
            Point(Vector::new([[-1, 1, -1]])),
            Point(Vector::new([[1, 1, -1]])),
            Point(Vector::new([[1, 1, 1]])),
            Point(Vector::new([[-1, 1, 1]])),
        ],
        color: ArcIntern::from("white"),
    };

    let x_rot = rotation_about(Vector::new([[-1, 0, 0]]), rotation_degree(1, 4).clone());

    let mut front = up.transformed(&x_rot);
    front.color = ArcIntern::from("green");
    let mut down = front.transformed(&x_rot);
    down.color = ArcIntern::from("yellow");

    let y_rot = rotation_about(Vector::new([[0, -1, 0]]), rotation_degree(1, 4).clone());

    let mut right = front.transformed(&y_rot);
    right.color = ArcIntern::from("red");
    let mut back = right.transformed(&y_rot);
    back.color = ArcIntern::from("blue");
    let mut left = back.transformed(&y_rot);
    left.color = ArcIntern::from("orange");

    Polyhedron(vec![up, right, down, left, front, back])
});

pub static DODECAHEDRON: LazyLock<Polyhedron> = LazyLock::new(|| {
    let φ = (Num::from(1) + Num::from(5).sqrt()) / Num::from(2);
    let φ_inv = Num::from(1) / φ.clone();

    let pentagon = Face {
        points: vec![
            Point(Vector::new([[φ_inv.clone(), φ.clone(), Num::from(0)]])),
            Point(Vector::new([[-φ_inv.clone(), φ.clone(), Num::from(0)]])),
            Point(Vector::new([[-1, 1, 1]])),
            Point(Vector::new([[Num::from(0), φ_inv, φ]])),
            Point(Vector::new([[1, 1, 1]])),
        ],
        color: ArcIntern::from("U"),
    };

    let mut centroid = pentagon.centroid();
    centroid.normalize_in_place();
    let [centroid] = centroid.into_inner();

    let [x, y, z] = centroid.clone();

    let rotate = Matrix::new([[1, 0, 0].map(Num::from), centroid, [x, -z, y]]);
    let derotate = rotate.transpose();

    let y_flip = rotation_about(Vector::new([[0, 1, 0]]), rotation_degree(1, 2).clone());
    let up = pentagon.transformed(&derotate);
    let mk_front = &derotate * &(&derotate * &y_flip);
    let mut front = up.transformed(&mk_front);
    front.color = ArcIntern::from("F");

    let y_rot = rotation_about(Vector::new([[0, 1, 0]]), rotation_degree(1, 5).clone());
    let mut right = front.transformed(&y_rot);
    right.color = ArcIntern::from("R");
    let mut back_1 = right.transformed(&y_rot);
    back_1.color = ArcIntern::from("BR");
    let mut back_2 = back_1.transformed(&y_rot);
    back_2.color = ArcIntern::from("BL");
    let mut left = back_2.transformed(&y_rot);
    left.color = ArcIntern::from("L");

    let top_half = vec![up, front, right, back_1, back_2, left];
    let around_x = rotation_about(Vector::new([[1, 0, 0]]), rotation_degree(1, 2).clone());
    let bottom_half = top_half
        .iter()
        .map(|v| v.transformed(&around_x))
        .zip(["D", "B", "DR", "FR", "FL", "DL"])
        .map(|(mut v, color)| {
            v.color = ArcIntern::from(color);
            v
        })
        .collect::<Vec<_>>();
    
    Polyhedron(top_half.into_iter().chain(bottom_half).collect())
});

pub static SHAPES: phf::Map<&'static str, &LazyLock<Polyhedron>> = phf::phf_map! {
    "c" => &CUBE,
    "t" => &TETRAHEDRON,
    "d" => &DODECAHEDRON,
};

pub fn print_shapes<'a>(shapes: impl Iterator<Item = &'a Face>) {
    println!("faces = [");
    for shape in shapes {
        print!("[");
        for Point(vertex) in &shape.points {
            print!("{:?},", vertex.inner()[0]);
        }
        print!("],");
    }
    println!("]");
}

#[cfg(test)]
mod tests {
    use crate::puzzle_geometry::shapes::*;

    #[test]
    fn shapes() {
        println!("{:?}", &*TETRAHEDRON);
        println!("{:?}", &*CUBE);
        println!("{:?}", &*DODECAHEDRON);
    }
}
