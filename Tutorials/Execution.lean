import Mathlib.Data.Fin.Basic
import Mathlib.Data.PNat.Basic

structure EvolvingProver where
  n : PNat
  State : Fin (n + 1) → Type
  Input : Fin n → Type
  Output : Fin n → Type
  step : (i : Fin n) → Input i → State i → (Output i × State i.succ)

theorem test {n : ℕ+} (i : Fin (n + 1)) (h : i = 0) : Fin.val i = 0 := by
  exact Fin.eq_mk_iff_val_eq.mp h

def runEvolvingProverAux {ep : EvolvingProver}
  (i : Fin (ep.n + 1))
  (inputs : (j : Fin i) → ep.Input j)
  (initialState : ep.State 0) :
  ((j : Fin i) → ep.Output j) × ep.State i :=
    if h : i = 0 then
      (λ j => False.elim (Fin.elim0 (Fin.cast (Fin.eq_mk_iff_val_eq.mp h) j)), h ▸ initialState)
    else
        let i' : Fin ep.n := Fin.pred i h
        let ⟨prevOut, prevState⟩ := runEvolvingProverAux i' (λ j => inputs (Fin.castLT j)) initialState
        let (output, nextState) := ep.step i' (inputs i') prevState
        (λ j =>
          if h' : j.val < i'.val then
            prev.1 (Fin.castLT j)
          else
            cast (by rw [show j = i' from Fin.eq_of_val_eq (Nat.le_antisymm (Nat.le_of_lt_succ (Fin.is_lt j)) (Nat.le_of_not_lt h'))]) output,
        nextState)

-- Example usage:
def exampleProver : EvolvingProver := {
  n := 3
  State := λ i => match i with
    | 0 => Nat
    | 1 => String
    | 2 => Bool
    | 3 => Unit
    | _ => Unit  -- This case is unreachable but needed for exhaustiveness
  Input := λ _ => Nat
  Output := λ _ => String
  step := λ i input state =>
    match i, state with
    | 0, s => ("Output 0", "State 1")
    | 1, s => ("Output 1", true)
    | 2, s => ("Output 2", ())
    | _ => ("", ())  -- This case is unreachable but needed for exhaustiveness
}

#eval runEvolvingProverAllRounds (λ _ => 0) 0
