-- import ZKLib.InteractiveOracleReduction.Basic
import VCVio

/-!
  # (Oracle) Commitment Schemes

  An (oracle) commitment scheme for a given oracle `Oracle : {D : Data} → Input → Output`
  parameterized by some data `D` consists of two main operations:

  - `commit` which commits to the data `D`
  - `open`, which is an interactive oracle proof (with respect to a different oracle `OraclePrime`)
    for the relation that `Oracle {D} (input) = output`. Here the underlying data `D` is the
    witness, and `input`, `output` are the statement.
-/


-- For now, define commitment schemes without oracles
-- For commitment schemes with oracles, we will need to define `commit`, `prove`, and `verify`
-- as `OracleComp` types

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


structure ListCommitmentSpec (R : Type) extends CommitmentSpec R where
  Datum : Type
  hData : Data = List Datum

structure ListCommitmentScheme (R : Type) extends ListCommitmentSpec R, CommitmentScheme R

-- @[simp]
-- lemma ListCommitmentSpec.hData_eq (cs : ListCommitmentSpec R) : cs.Data = List cs.Datum := cs.hData



variable {R : Type} [Mul R] [Inhabited R]

def test : CommitmentSpec R where
  Data := R
  Randomness := R
  Query := R
  Response := R
  OpeningFunction := fun data query => data * query
  Commitment := R
  Proof := R

def testListCom : ListCommitmentSpec R where
  Datum := R
  Data := List R
  Randomness := R
  Query := R
  Response := R
  OpeningFunction := fun data query => List.foldl (fun x y => x * y) query data
  Commitment := R
  Proof := R
  hData := rfl

-- Lean only reduces definitional equality, not propositional equality
def MyNat := Nat

def exampleFunction (n : Nat) : MyNat := n

#check exampleFunction 5


namespace test

structure CommitmentSpec where
  Data : Type
  Randomness : Type
  Commitment : Type

structure ListCommitmentSpec where
  Datum : Type
  Randomness : Type
  Commitment : Type

def ListCommitmentSpec.Data (cs : ListCommitmentSpec) : Type := List cs.Datum

def ListCommitmentSpec.toCommitmentSpec (cs : ListCommitmentSpec) : CommitmentSpec :=
  {
    Data := cs.Data
    Randomness := cs.Randomness
    Commitment := cs.Commitment
  }

instance : Coe ListCommitmentSpec CommitmentSpec where
  coe := ListCommitmentSpec.toCommitmentSpec

end test
