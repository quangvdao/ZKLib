
# Roadmap

We provide a (non-exhaustive) list of tasks to be completed:

- [ ] [`Data`](ZKLib/Data)
  - [ ] [`ComputablePolynomial`](ZKLib/Data/ComputablePolynomial)
    - [ ] [`Multilinear.lean`](ZKLib/Data/ComputablePolynomial/Multilinear.lean)
      - [ ] Define & verify operations to convert between evaluation basis (what we call `MlPoly`) and coefficient basis (to be defined).
      - [ ] Define a `Module` instance for `MlPoly`
      - [ ] Define & prove equivalence between `MlPoly` and `MvPolynomial` whose individual degrees are restricted to be at most 1 (see Mathlib for the definition).
    - [ ] [`Univariate.lean`](ZKLib/Data/ComputablePolynomial/Univariate.lean)
      - [ ] Similar tasks to `Multilinear.lean` but for univariate polynomials.
      - [ ] Consider representing polynomials as `Array` instead of `List` to improve performance.
  - [ ] [`MvPolynomial`](ZKLib/Data/MvPolynomial)
    - [ ] [`Interpolation.lean`](ZKLib/Data/MvPolynomial/Interpolation.lean)
      - [ ] Develop the theory of interpolating multivariate polynomials given their values on a `n`-dimensional grid of points.
      - [ ] Specialize this theory to the case of multilinear polynomials (then merge with [`Multilinear.lean`](ZKLib/Data/MvPolynomial/Multilinear.lean)).
        - There is some subtlety here in the sense that general interpolation requires a field (for inverses of Lagrange coefficients), but multilinear interpolation/extension only requires a ring (since the coefficients are just `1`). We may need to develop multilinear theory for non-fields (for Binius).
  - [ ] [`BinaryTowerField`](ZKLib/Data/BinaryTowerField)
    - [ ] Define iterated quadratic extensions of the binary field (Wiedermann construction), and prove that the resulting ring is a field.
    - [ ] Define efficient representation of elements in a binary tower field (using `BitVec`?), (efficient) operations on them (see Binius paper), and prove that the resulting structure is a field isomorphic to the definition above.
  - [ ] [`ScalarPrimeField`](ZKLib/Data/ScalarPrimeField)
    - [ ] Override operations on prime fields with verified implementations by e.g. fiat-crypto.
  - [ ] [`EllipticCurve`](ZKLib/Data/EllipticCurve/)
    - [ ] Consider importing [`FFaCiL`](https://github.com/argumentcomputer/FFaCiL.lean/tree/main) and improving upon it.
    - [ ] Need to prove statements of the form "this elliptic curve over `F_q` has a large prime-order subgroup isomorphic to `F_p`".
