# A Library for Formally Verified Cryptographic Proof Systems

We provide a generic framework for formally verifying cryptographic proof systems that are compiled from interactive (oracle) proofs via the Fiat-Shamir transform and (polynomial) commitment schemes.

In the first stage of the project, we formalize interactive (oracle) proofs, and prove information-theoretic completeness and soundness for the class of multilinear-based proof systems.

In particular, we aim to formalize the [sum-check protocol](https://dl.acm.org/doi/10.1145/146585.146605) and [Spartan](https://eprint.iacr.org/2019/550), both as polynomial IOPs. We also plan to formalize the tensor-based polynomial commitment scheme (PCS), underlying [Ligero](https://eprint.iacr.org/2022/1608), [Brakedown](https://eprint.iacr.org/2021/1043), and [Binius](https://eprint.iacr.org/2023/1784), and prove that Spartan when composed with such a PCS forms a complete & sound interactive proof system.

For each protocol mentioned above, we aim to provide:

- A specification based on (multivariate) polynomials from `Mathlib`,
- An implementation of the prover and verifier using computable representations of polynomials (see [`Data`](./ZKLib/Data/)), similar to Rust implementations,
- Proofs of completeness and round-by-round soundness for the specification, and proof that the implementation refines the specification.

In future stages, we plan to extend the set of proof systems formalized using our framework, including other hash-based SNARKs based on univariate PCS (e.g. STARKs with [FRI](https://drops.dagstuhl.de/storage/00lipics/lipics-vol107-icalp2018/LIPIcs.ICALP.2018.14/LIPIcs.ICALP.2018.14.pdf) / [STIR](https://eprint.iacr.org/2024/390)), and other proof systems based on discrete-log or pairings (e.g. [Plonk](https://eprint.iacr.org/2019/953), Spartan with [Hyrax](https://eprint.iacr.org/2017/1132), or [Nova](https://eprint.iacr.org/2021/370)).

## Roadmap

See [ROADMAP (somewhat outdated)](./ROADMAP.md), and the list of issues.

We welcome outside contributions to the library! If you're interested in working on any of the items mentioned in the list of issues or the roadmap, please contact [the authors](mailto:qvd@andrew.cmu.edu) or open a new issue.