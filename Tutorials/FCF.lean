-- import Mathlib.Tactic.Common
-- import Mathlib.Control.Random
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Finset.Card

/-!
  # The Foundational Cryptographic Framework (FCF)

  This is a port from the FCF library in Coq to Lean. We make no attempt at completeness, rather we only port enough for our goal of mechanizing proof systems.
-/


namespace Crypto

section Comp

-- Probabilistic computation
inductive Comp : Type _ → Type _ where
  -- return a value of type A
  | pure [DecidableEq A] : A → Comp A
  -- continue the computation
  | bind : Comp B → (B → Comp A) → Comp A
  -- sample uniformly among some non-empty finite type with decidable equality
  | rand [Fintype A] [Inhabited A] [DecidableEq A] : Comp A
  -- repeat until some deciable predicate returns true
  | repeat : Comp A → (A → Bool) → Comp A

-- Can't define monad instance since `DecidableEq` gets in the way
-- instance : Monad Comp where
--   pure := Comp.pure
--   bind := Comp.bind

@[simp]
def compExists {A : Type _} (x : Comp A) : A :=
  match x with
    | Comp.pure y => y
    | Comp.bind y f => compExists (f (compExists y))
    | Comp.rand => default
    | Comp.repeat y _ => compExists y

instance instCompDecidableEq {A : Type _} (x : Comp A) : DecidableEq A :=
  match x with
    | Comp.pure _ => inferInstance
    | Comp.bind y f => instCompDecidableEq (f (compExists y))
    | Comp.rand => inferInstance
    | Comp.repeat y _ => instCompDecidableEq y

instance instCompBindDecidableEq {A B : Type _} (x : Comp B) (f : B → Comp A) : DecidableEq A :=
  instCompDecidableEq (Comp.bind x f)

def getSupport {A : Type _} (x : Comp A) : Finset A :=
  match x with
    | Comp.pure y => {y}
    | Comp.bind y f => @Finset.biUnion _ _ (instCompBindDecidableEq y f) (getSupport y) (fun x => getSupport (f x))
    | Comp.rand => Finset.univ
    | Comp.repeat y _ => getSupport y

-- @[simp]
theorem getSupport_pure_iff [DecidableEq A] (x a : A) : x ∈ getSupport (Comp.pure a) ↔ x = a := by simp [getSupport]

-- @[simp]
theorem getSupport_bind_iff (x : Comp B) (f : B → Comp A) (a : A) : a ∈ getSupport (Comp.bind x f) ↔ ∃ b ∈ getSupport x, a ∈ getSupport (f b) := by simp [getSupport]


inductive wellFormedComp {A : Type _} : Comp A → Prop where
  | wfPure [DecidableEq A] : wellFormedComp (Comp.pure x)
  | wfBind : (x : Comp B) → (f : B → Comp A) → wellFormedComp (Comp.bind x f) -- add more conditions
  | wfRand [Fintype A] [Inhabited A] [DecidableEq A] : wellFormedComp Comp.rand
  | wfRepeat [DecidableEq A] : (x : Comp A) → (p : A → Bool) → (∀ b, wellFormedComp x → b ∈ Finset.filter p (getSupport x)) → wellFormedComp (Comp.repeat x p)


@[simp]
theorem wellFormedExists (x : Comp A) (h : wellFormedComp x) : ∃ a, a ∈ getSupport x := sorry

@[simp]
theorem getSupport_card_pos {A : Type _} (x : Comp A) (h : wellFormedComp x) : (getSupport x).card > 0 := sorry

end Comp


section CompEq

-- Syntactic equality for `Comp`
inductive CompEq : Comp A → Comp A → Prop where
  | eqPure [DecidableEq A] : CompEq (@Comp.pure A _ x) (@Comp.pure A _ x)
  | eqBind : CompEq x y → (∀ b, CompEq (f b) (g b)) → CompEq (Comp.bind x f) (Comp.bind y g)
  | eqRand [Fintype A] [Inhabited A] [DecidableEq A] : CompEq (@Comp.rand A _ _ _) (@Comp.rand A _ _ _)
  | eqRepeat : CompEq x y → (∀ a, p a = q a) → CompEq (Comp.repeat x p) (Comp.repeat y q)

@[simp]
theorem comp_eq_refl (x : Comp A) : CompEq x x := match x with
  | Comp.pure _ => CompEq.eqPure
  | Comp.bind x f => CompEq.eqBind (comp_eq_refl x) (λ b => comp_eq_refl (f b))
  | Comp.rand => CompEq.eqRand
  | Comp.repeat x _ => CompEq.eqRepeat (comp_eq_refl x) (λ _ => rfl)




end CompEq


section OracleComp

-- Probabilistic computation with access to a stateful oracle
inductive OracleComp : Type _ → Type _ → Type _ → Type _ where
  -- give oracle access to some probabilistic computation
  | pure : Comp C → OracleComp A B C
  -- continue the oracle computation
  | bind : OracleComp A B C' → (C' → OracleComp A B C) → OracleComp A B C
  -- query the oracle with query of type `A`, and get the result of type `B`
  | query : A → OracleComp A B B
  -- run the program under a different oracle that is allowed to access the current oracle
  | run [DecidableEq A] [DecidableEq B] [DecidableEq S] : OracleComp A B C → S → (S → A → OracleComp A' B' (B × S)) → OracleComp A' B' (C × S)

-- ehh, again due to `DecidableEq` getting in the way
-- instance : Monad (OComp A B) where
--   pure := OComp.pure ∘ Comp.pure
--   bind := OComp.bind

@[simp]
def oracleCompToComp (x : OracleComp A B C) : (A → B) → C := fun f =>
  match x with
    | OracleComp.pure y => compExists y
    | OracleComp.bind y g => oracleCompToComp (g (oracleCompToComp y f)) f
    | OracleComp.query a => f a
    | @OracleComp.run A' B' S C' _ _ _ _ _ x s o =>
      let IHX := oracleCompToComp x
      let H := fun s a g => oracleCompToComp (o s a) g
      let X0 := o s
      let H1 := H s
      let H2 :=
        let H2 :=
        (fun (H2 : B' -> C') (H3 : A') =>
          let X1 := X0 H3
          let H4 := H1 H3
          let H5 := H4 f
          Prod.recOn (motive := fun _ : B' × S => B') H5
            (fun (a : B') (_ : S) => let H6 := H2 a ; a))
        (fun y : B' => IHX (fun _ : A' => y))
        IHX H2 (fun H3 : C => H3)
      ⟨H2, s⟩

instance oracleCompDecidableEq (x : OracleComp A B C) (f : A → B) (g : A → DecidableEq B) : DecidableEq C := sorry


end OracleComp

section Map



end Map



end Crypto


-- other stuff from call with Josh

-- Probability trees
inductive PTree : Type → Type where
  | return : A → PTree A
  | flip : (Bool → PTree A) → PTree A

-- Interaction trees
inductive ITree (E : Type _ → Type _) (R : Type _) : Type _ where
  | ret : R → ITree E R
  | tau : ITree E R → ITree E R
  | event : (E A) → (A → ITree E R) → ITree E R
