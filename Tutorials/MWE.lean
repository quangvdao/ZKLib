-- Minimum working example (MWE) to post on Zulip

structure myStruct where
  m : Nat
  n : Nat
  p := m + n
  funA : Fin p → Nat
  funB : Fin p → Bool

/-
type mismatch
  Iff.rfl
has type
  ?m.669 ↔ ?m.669 : Prop
but is expected to have type
  S.3 = S.m + S.n : Prop
-/

def (S : myStruct) : Fin p → Nat where p := S.m + S.n
