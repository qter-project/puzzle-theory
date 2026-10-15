⭐means it's important to be done before the video series
😎means it's optional

## Schreier Sims

- ⭐Optimal stabilizer chain
  - Bookmark: https://dl.acm.org/doi/10.1145/281508.281611
- Allow variations in the number of pieces solved by each link in the chain
- Create a heuristic for picking which pieces to solve in which order
- Assess feasibility of generalizing Thisthethwaite-like methods to arbitrary puzzles
- NISS
- Trembling

## PuzzleGeometry

- Canonical signature facelet choosing
  - Optimal in a meaningful sense
- ⭐Detect identical pieces
- ⭐Implement better face cutting algorithm
- ⭐Calculate orientation and parity constraints of the puzzle
- ⭐Calculate the symmetries of the puzzle
- Figure out algebraics
  - Acceptance criterion: All default puzzles can be processed in <1s with exact arithmetic
  - Remove usages of square roots and use a field extension instead of algebraics
- Parse our modified puzzlegeometry definition string
- Spherical cuts
- Make the ksolve stuff zero indexed

### GRIP THEORY REFACTOR IDEATION

- `PuzzleGeometryDefinition`
  - Converts to `GripTheoryRepr`
    - Expresses each piece as a collection of 1x1's where the grip group is represented as a set of orthogonal matrices
    - Supports binding and shapeshifting
    - Converts to `FiniteGripTheoryRepr`
      - Grip group is a cayley table or some other finite group repr
      - Supports SIMD composition?
      - Converts to `NonBindingGripTheoryRepr`
        - Binding is checked for and erased
        - Converts to `KSolvePuzzle`
        - Converts to our current `PuzzleGeometry`
          - Shapeshifting is checked for and erased
          - Converts to `PermutationGroup` on stickers

#### Open questions

- Definition format
  - Cannot autodetect rotation angles
    - How do we specify them?
  - Rhai as definition language?
- SIMD composition of grip theory reprs
  - How _exactly_ would that work?
- What do we do about `algebraics`?
  - It's possible to have rotation angles that are non-algebraic
  - Arbitrary field extension?
  - f128?
  - f64?
- Should we factor puzzlegeometry out of this repo? It's getting quite big
- Should we support arbitrary dimensional puzzles?
  - Probably no bc quaternions

## Misc

- Refactor the ksolve format
  - Zero based
  - Don't require `PuzzleGeometry::ksolve` to do casts
- Replace internment with sarlacc and newtype some intern types
- Remove the `Point` newtype
- 😎Refactor spans to form a tree structure

