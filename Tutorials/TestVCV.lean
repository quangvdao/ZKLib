import VCVio

open Sum Polynomial OracleSpec OracleComp

variable {α β γ : Type} [Inhabited β] [Fintype β]
    [DecidableEq β] [DecidableEq α] [Inhabited γ] [Fintype γ]

-- Given a computation that answers queries, construct a `SimOracle`
def statelessOracle {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (f : (i : ι) → spec.domain i → OracleComp spec' (spec.range i)) :
    spec →[Unit]ₛₒ spec' :=
  λ i t () ↦ (·, ()) <$> f i t

-- turn a function into an oracle implementation, while logging queries
-- the stateless oracle introduces a useless `Unit` to the internal state which we mask
-- `simulate` with this will answer queries with `f` and log input and outputs
def oracleize (f : α → β) : (α →ₒ β) →[QueryLog (α →ₒ β)]ₛₒ (α →ₒ β) :=
  (loggingOracle ∘ₛₒ statelessOracle (λ () t ↦ return f t)).maskState
    (Equiv.punitProd (α →ₒ β).QueryLog)



-- Lifting a deterministic function `f: α → β` to an oracle that keeps track of the queries
-- def oracleize (f : α → β) : SimOracle (α →ₒ β) (α →ₒ β) (QueryLog (α →ₒ β)) :=
--   fun _ a log => do
--     let b := f a
--     return (b, QueryLog.logQuery log a b)

-- Testing the oracle-ize operation
def testOracleize (f : α → β) (a : α) : OracleComp (α →ₒ β) (β × (α →ₒ β).QueryLog) := do
  let (y, s) ← simulate (oracleize f) (fun _ => []) (pure (f a))
  let (z, s') ← simulate (oracleize f) s (pure y)
  return (z, s')

#check testOracleize (fun (x : Bool) => Not x) true

-- #eval OracleComp.runIO (runDeterministic (fun (x : Bool) => not x) true)
-- Since the computation is deterministic, can I return the actual value?


-- Well... since all I really need is to add a wrapper to a function, that additionally keeps track of the queries, I could just define my own thing
-- inductive OracleWithLog {α β : Type} (log : List (α × β)) : Type where
--   | init : OracleWithLog (List.nil)
--   | query : (a : α) → OracleWithLog log → OracleWithLog (log ++ [(a, f a)])
--   | return : β → OracleWithLog log


variable {R : Type} [Semiring R]
  [Fintype R] [DecidableEq R] [Inhabited R]
  [SelectableType R]

-- Second oracle take in values in `R` and "evaluate" the polynomial on them
-- At this point oracle is a black box, no actual behavior specified
-- But for the purpose of defining the computation that isn't needed
def test : OracleComp (unifSpec ++ₒ (R →ₒ R)) R := do
  let x₁ : R ←$ᵗ R
  let x₂ : R ←$ᵗ R
  -- Query the `inr` oracle to evaluate polynomial on some values
  let query_result₁ : R ← query (inr ()) (x₁ + x₂)
  let query_result₂ : R ← query (inr ()) (x₁ + 2 * x₂)
  return query_result₁ + query_result₂

-- `SimOracle` for actually implementing oracle behavior
-- Simulates the oracle `R →ₒ R` by evaluating the polynomial on queries
-- This reduces the oracles to just `unifSpec` (although really anything could go there)
-- Assumes the polynomial is globally fixed so just take `p` as input
-- No internal state so we use `Unit` type for that
def polyEvalOracle (p : R[X]) : (R →ₒ R) →[Unit]ₛₒ emptySpec :=
  λ () t () ↦ do
    let eval_result := p.eval t
    return (eval_result, ())

-- Run a computation `oa : OracleComp (unifSpec ++ₒ (R →ₒ R)) α` using the above
-- `polyGenerator` is the computation that produces the polynomial to use for oracle
noncomputable example (p : R[X])
    (oa : OracleComp (R →ₒ R) α) :
    OracleComp emptySpec α := do
  let x ← simulate' (idOracle ++ₛₒ polyEvalOracle p) ((), ()) oa
  return x

-- Version that stores the polynomial in state of the oracle
-- Only needed if the polynomial being used will change during the execution
def polyEvalOracle_state : (R →ₒ R) →[R[X]]ₛₒ unifSpec :=
  λ () t p ↦ do
    let eval_result := p.eval t
    return (eval_result, p) -- Could modify the internal polynomial `p` first
