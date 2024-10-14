import ZKLib.OracleReduction.Basic
import VCVio

/-!
  # Oracle Commitment Schemes

  A commitment scheme for a given oracle `Oracle : {D : Data} → Input → Output`
  parameterized by some data `D` consists of two main operations:

  - `commit` which commits to the data `D`
  - `open`, which is an interactive oracle proof (with respect to a different oracle `OraclePrime`)
    for the relation that `Oracle {D} (input) = output`. Here the underlying data `D` is the
    witness, and `input`, `output` are the statement.
-/

namespace Commitment

open OracleSpec OracleComp

-- We may not be able to say that the opening of a commitment scheme is an IOP for some relation, because that relation may require querying oracles to determine validity.

structure Spec where
  Data : Type
  Commitment : Type
  Query : Type
  Response : Type
  eval : Data → Query → Response
  n : ℕ
  Opening : ProtocolSpec n

structure Commit (CSpec : Spec) (OSpec : OracleSpec ι) (State : Type) where
  commit : CSpec.Data → StateT State (OracleComp OSpec) CSpec.Commitment

structure Prover (CSpec : Spec) (OSpec : OracleSpec ι) (State : Type) extends ProverRound CSpec.Opening OSpec State where
  loadState : CSpec.Data → CSpec.Query → State

structure Scheme (CSpec : Spec) (OSpec : OracleSpec ι) (State : Type) extends
    Prover CSpec OSpec State,
    Verifier CSpec.Opening OSpec (CSpec.Commitment × CSpec.Query × CSpec.Response)

-- /-- The opening relation for a commitment scheme.
-- Shows that `c` is a commitment to some `data`, whose oracle representation takes in `query` and outputs `response`. -/
-- def relation (oSpec : OracleSpec ι) (cSpec : Spec oSpec) : OracleRelation oSpec where
--   Statement := cSpec.Commitment × cSpec.Query × cSpec.Response
--   Witness := cSpec.Data
--   isValid := fun ⟨commitment, query, response⟩ data =>
--     (cSpec.eval data query = response ∧ commitment = ·) <$> cSpec.commit data


section Security

-- Define binding, extractability, hiding

def binding (CSpec : Spec) (OSpec : OracleSpec ι) (State : Type) (Statement : Type) (Witness : Type) (Scheme : Scheme CSpec OSpec State) : Prop := sorry

def extractability (CSpec : Spec) (OSpec : OracleSpec ι) (State : Type) (Statement : Type) (Witness : Type) (Scheme : Scheme CSpec OSpec State) : Prop := sorry

def hiding' (CSpec : Spec) (OSpec : OracleSpec ι) (State : Type) (Statement : Type) (Witness : Type) (Scheme : Scheme CSpec OSpec State) : Prop := sorry


end Security


end Commitment
