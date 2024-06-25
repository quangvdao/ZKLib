# Formal Verification of Jolt

The goal of this project is to formalize the information-theoretic components of Jolt, a "zero-knowledge" virtual machine (zkVM) for the RISC-V ISA.

In particular, we formalize the following protocols:

- Sumcheck
- Spartan
- GKR
- Grand Product Argument
- Lasso Lookup Argument
- Spice Memory Checking Argument

For each protocol, seen as interactive proofs, we provide an implementation of the prover and verifier, and prove completeness and round-by-round soundness with tight bounds.

Along the way, we also formalize notions of interactive oracle proofs/reductions, multilinear polynomials, and binary tower fields.