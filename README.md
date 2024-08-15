# A Library for Formally Verified Cryptographic Proof Systems

We provide a formalization of cryptographic proof systems that are compiled from interactive (oracle) proofs via the Fiat-Shamir transform and (polynomial) commitment schemes.

In the first stage of the project, we formalize interactive (oracle) proofs, and prove information-theoretic completeness and soundness for the class of multilinear-based proof systems. In particular, our scope includes the following protocols:
- Sum-check
- Spartan
- GKR and variants
- Grand Product Argument
- Lasso Lookup Argument
- Spice Memory Checking Argument

In addition, we also plan to formalize the following polynomial commitment schemes, seen as interactive (oracle) proofs:
- Ligero and follow-ups such as Brakedown and Binius
- Hyrax

The protocols above form the core components of the Jolt zero-knowledge virtual machine (zkVM). A long-term goal of this project is to fully formalize the Jolt zkVM.

For each interactive protocol, we aim to provide:
- A specification based on (multivariate) polynomials from `Mathlib`,
- An implementation of the prover and verifier using computable encodings of polynomials, similar to Rust implementations,
- Proofs of completeness and round-by-round soundness for the specification, proof that the implementation refines the specification.