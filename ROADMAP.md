
# Roadmap

We provide a (non-exhaustive) list of tasks to be completed. Our focus here is mostly on `Data`, since it is the part that can be most easily be contributed to by outside contributors.

- [ ] [`Data`](ZKLib/Data)
  - [ ] [Miscellaneous](ZKLib/Data/Misc)
    - [ ] This folder is meant to be the place to store any definitions or theorems about `Mathlib` data types (e.g. `List` and `Array`) that are required in other parts of the library.
  - [ ] [Computable Univariate Polynomials](ZKLib/Data/UniPoly)
    - [x] Define `UniPoly` as the type of univariate polynomials with computable representations (interally as an `Array` of coefficients). Define operations on `UniPoly` as operations on the underlying `Array` of coefficients.
    - [x] Define an equivalence relation on `UniPoly` that says two `UniPoly`s are equivalent iff they are equal up to zero-padding. Show that this is an equivalence relation.
    - [ ] Show that operations on `UniPoly` descends to the quotient (i.e. are the same up to zero-padding). Show that the quotient is isomorphic as semirings to `Polynomial` in `Mathlib`. Show that the same functions (e.g. `eval`) on `UniPoly` are the same as those of `Polynomial`.
    - [ ] For more efficient evaluation, and use in univariate-based SNARKs, define the coefficient representation of `UniPoly` (on `2`-adic roots of unity), and show conversions between the coefficient and evaluation representations.
  - [ ] [Computable Multilinear Polynomials](ZKLib/Data/MlPoly)
    - [ ] Define `MlPoly` as the type of multilinear polynomials with computable representations (internally as an `Array` of coefficients). Define operations on `MlPoly` as operations on the underlying `Array` of coefficients.
    - [ ] Define alternative definition of `MlPoly` where the evaluations on the hypercube are stored instead of the coefficients. Define conversions between the two definitions, and show that they commute with basic operations.
      - [ ] Will need to expand `Mathlib`'s support for indexing by bits (i.e. further develop `BitVec`).
    - [ ] Define an equivalence relation on `MlPoly` that says two `MlPoly`s are equivalent iff they are equal up to zero-padding. Show that this is an equivalence relation. Show that operations on `MlPoly` descends to the quotient.
    - [ ] Define & prove a module isomorphism between the quotient of `MlPoly` by the equivalence relation and `MvPolynomial` whose individual degrees are restricted to be at most 1.
  - [ ] [Extensions to Multivariate Polynomials in `Mathlib`](ZKLib/Data/MvPolynomial)
    - [ ] [`Interpolation.lean`](ZKLib/Data/MvPolynomial/Interpolation.lean)
      - [ ] Develop the theory of interpolating multivariate polynomials given their values on a `n`-dimensional grid of points.
      - [ ] Specialize this theory to the case of multilinear polynomials (then merge with [`Multilinear.lean`](ZKLib/Data/MvPolynomial/Multilinear.lean)).
        - There is some subtlety here in the sense that general interpolation requires a field (for inverses of Lagrange coefficients), but multilinear interpolation/extension only requires a ring (since the coefficients are just `1`). We may need to develop multilinear theory for non-fields (for Binius).
  - [ ] [Coding Theory](ZKLib/Data/CodingTheory)
    - [ ] Define and develop basic results on linear codes.
    - [ ] Define basic codes such as Reed-Solomon.
    - [ ] Prove proximity gap and interleaved distance results (up to one-third of the unique decoding distance).
  - [ ] [Binary Tower Fields](ZKLib/Data/BinaryTowerField)
    - [ ] Define iterated quadratic extensions of the binary field (Wiedermann construction), and prove that the resulting ring is a field.
    - [ ] Define efficient representation of elements in a binary tower field (using `BitVec`), efficient operations on them (see Binius paper), and prove that the resulting structure is a field isomorphic to the definition above.
  - [ ] [Large Scalar Fields used in Curves](ZKLib/Data/ScalarPrimeField)
    - [ ] Low-priority for now.
    - [ ] Development on this should be done over at [`FFaCiL`](https://github.com/argumentcomputer/FFaCiL.lean/tree/main).
- [ ] [`InteractiveOracleReduction`](ZKLib/InteractiveOracleReduction)
  - In this folder, we define Interactive Oracle Reductions (IOR) as the basic building block of proof systems. This is the same as an IOP, except that we are using interaction to reduce one (oracle) relation to another. This allows us to reason modularly about the security properties of proof systems.
  - The main definitions are in [`Basic.lean`](ZKLib/InteractiveOracleReduction/Basic.lean). We plan to define the composition of two IORs (with matching oracle relations) in [`Composition.lean`](ZKLib/InteractiveOracleReduction/Composition.lean). We also plan to define composition of an IOR with commitment schemes for the corresponding oracles.
- [ ] [`ProofSystem`](ZKLib/ProofSystem)
  - In this folder, we plan to provide the specification and implementation of the sum-check protocol (in [`SumCheck.lean`](ZKLib/ProofSystem/Sumcheck)) and Spartan (in [`Spartan.lean`](ZKLib/ProofSystem/Spartan)).
- [ ] [`CommitmentScheme`](ZKLib/CommitmentScheme)
  - [ ] In [`Basic.lean`](ZKLib/CommitmentScheme/Basic.lean), we plan to provide the basic definition of an oracle commitment scheme, where the opening procedure may itself be an IOP with access to some other oracles (e.g. random oracles).
  - [ ] In [`Tensor.lean`](ZKLib/CommitmentScheme/Tensor.lean), we plan to provide a construction of the tensor-based polynomial commitment scheme underlying Ligero, Brakedown, Binius, etc. The opening procedure of this PCS then takes the form of an IOP where the messages are available as point queries (e.g. the messages are vectors, and one can query individual positions of the messages).
  - [ ] In [`MerkleTree.lean`](ZKLib/CommitmentScheme/MerkleTree.lean), we provide a construction of Merkle trees, where hashing are modeled as random oracle queries, as an example of a vector commitment scheme. This can then be composed with the tensor-based PCS above to form an interactive PCS in the random oracle model. We plan to show the extractability and privacy of Merkle trees as in [this hash-based SNARGs textbook](https://github.com/hash-based-snargs-book/hash-based-snargs-book).