# Formal Verification of Jolt

The goal of this project is to formalize the information-theoretic components of Jolt, a "zero-knowledge" virtual machine (zkVM) for the RISC-V ISA.

In particular, we formalize the following protocols:

- Sumcheck
- Spartan
- Grand Product Argument
- Lasso Lookup Argument
- Spice Memory Checking Argument

For each protocol, seen as interactive proofs, we provide an implementation of the prover and verifier, and prove completeness and soundness with tight soundness bounds.

Along the way, we also formalize notions of interactive proofs/reductions, multilinear polynomials, and binary tower fields.


## MIT License

Copyright © 2024 Quang Dao

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the “Software”), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.