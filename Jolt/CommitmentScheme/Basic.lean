-- import Jolt.InteractiveOracleReduction.Basic

/-!
  # (Oracle) Commitment Schemes

  An (oracle) commitment scheme for a given oracle `Oracle : {D : Data} → Input → Output`
  parameterized by some data `D` consists of two main operations:

  - `commit` which commits to the data `D`
  - `open`, which is an interactive oracle proof (with respect to a different oracle `OraclePrime`)
    for the relation that `Oracle {D} (input) = output`. Here the underlying data `D` is the
    witness, and `input`, `output` are the statement.
-/

structure CommitmentSpec (R : Type) where
  Data : Type
  Randomness : Type
  Query : Type
  Response : Type
  OpeningFunction : Data → Query → Response
  Commitment : Type
  Proof : Type

structure CommitmentScheme (R : Type) extends CommitmentSpec R where
  commit : Data → Randomness → Commitment
  prove : Data → Randomness → Commitment → Query → Response → Proof
  verify : Commitment → Query → Response → Proof → Bool

variable {R : Type} [Mul R]

def test : CommitmentSpec R where
  Data := R
  Randomness := R
  Query := R
  Response := R
  OpeningFunction := fun data query => data * query
  Commitment := R
  Proof := R
