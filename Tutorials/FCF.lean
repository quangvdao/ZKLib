import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Finset.Card

/-!
  # The Foundational Cryptographic Framework (FCF)

  This is a port from the FCF library in Coq to Lean. We make no attempt at completeness, rather we only port enough for our goal of mechanizing proof systems.
-/


namespace Crypto

/-
'DecidableEq' is not a structure
-/
-- class Sampleable (A : Type _) extends Fintype A, Inhabited A, DecidableEq A

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

instance instCompDecEq {A : Type _} (x : Comp A) : DecidableEq A :=
  match x with
    | Comp.pure _ => inferInstance
    | Comp.bind y f => instCompDecEq (f (compExists y))
    | Comp.rand => inferInstance
    | Comp.repeat y _ => instCompDecEq y

instance instCompBindDecEq {A B : Type _} (x : Comp B) (f : B → Comp A) : DecidableEq A :=
  instCompDecEq (Comp.bind x f)

def getSupport {A : Type _} (x : Comp A) : Finset A :=
  match x with
    | Comp.pure y => {y}
    | Comp.bind y f => @Finset.biUnion _ _ (instCompBindDecEq y f) (getSupport y) (fun x => getSupport (f x))
    | Comp.rand => Finset.univ
    | Comp.repeat y _ => getSupport y

@[simp]
theorem getSupport_pure_iff [DecidableEq A] (x a : A) : x ∈ getSupport (Comp.pure a) ↔ x = a := by simp [getSupport]

@[simp]
theorem getSupport_bind_iff (x : Comp B) (f : B → Comp A) (a : A) : a ∈ getSupport (Comp.bind x f) ↔ ∃ b ∈ getSupport x, a ∈ getSupport (f b) := by simp [getSupport]


inductive wellFormed : ∀ A, Comp A → Prop where
  | pure [DecidableEq A] : wellFormed A (Comp.pure x)
  | bind : (x : Comp B) → (f : B → Comp A) → wellFormed B x → (∀ b, b ∈ getSupport x → wellFormed A (f b)) → wellFormed A (Comp.bind x f)
  | rand [Fintype A] [Inhabited A] [DecidableEq A] : wellFormed A Comp.rand
  | repeat [DecidableEq A] : (x : Comp A) → wellFormed A x → (p : A → Bool)
    → ∀ b : A, b ∈ Finset.filter (fun x => p x = true) (getSupport x)
      → wellFormed A (Comp.repeat x p)

@[simp]
theorem wellFormedExists (x : Comp A) (h : wellFormed A x) : ∃ a, a ∈ getSupport x := match x with
  | Comp.pure y => ⟨y, Finset.mem_singleton_self y⟩
  | Comp.bind y f => match h with
    | wellFormed.bind _ _ hy hf =>
      let ⟨b, hb⟩ := wellFormedExists y hy
      let ⟨a, ha⟩ := wellFormedExists (f b) (hf b hb)
      ⟨a, getSupport_bind_iff y f a |>.mpr ⟨b, hb, ha⟩⟩
  | Comp.rand => ⟨default, Finset.mem_univ _⟩
  | Comp.repeat y p => match h with
    | wellFormed.repeat _ _ _ b hp =>
      ⟨b, getSupport y |>.filter_subset (fun x => p x = true) hp⟩

@[simp]
theorem getSupport_card_pos {A : Type _} (x : Comp A) (h : wellFormed A x) : (getSupport x).card > 0 := by
  obtain ⟨a, ha⟩ := wellFormedExists x h
  exact Finset.card_pos.mpr ⟨a, ha⟩

end Comp


section CompEq

-- Syntactic equality for `Comp`
inductive CompEq : Comp A → Comp A → Prop where
  | pure [DecidableEq A] : CompEq (@Comp.pure A _ x) (@Comp.pure A _ x)
  | bind : CompEq x y → (∀ b, CompEq (f b) (g b)) → CompEq (Comp.bind x f) (Comp.bind y g)
  | rand [Fintype A] [Inhabited A] [DecidableEq A] : CompEq (@Comp.rand A _ _ _) (@Comp.rand A _ _ _)
  | repeat : CompEq x y → (∀ a, p a = q a) → CompEq (Comp.repeat x p) (Comp.repeat y q)

@[simp]
theorem comp_eq_refl (x : Comp A) : CompEq x x := match x with
  | Comp.pure _ => CompEq.pure
  | Comp.bind x f => CompEq.bind (comp_eq_refl x) (λ b => comp_eq_refl (f b))
  | Comp.rand => CompEq.rand
  | Comp.repeat x _ => CompEq.repeat (comp_eq_refl x) (λ _ => rfl)




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
def oracleCompExists (x : OracleComp A B C) : (A → B) → C := fun f =>
  match x with
    | OracleComp.pure y => compExists y
    | OracleComp.bind y g => oracleCompExists (g (oracleCompExists y f)) f
    | OracleComp.query a => f a
    | OracleComp.run y s o =>
      let g := fun x => Prod.fst (oracleCompExists (o s x) f)
      ⟨ oracleCompExists y g, s ⟩

instance oracleCompDecEq (x : OracleComp A B C) (f : A → B) (g : A → DecidableEq B) : DecidableEq C := match x with
  | OracleComp.pure y => instCompDecEq y
  | OracleComp.bind y h => oracleCompDecEq (h (oracleCompExists y f)) f g
  | OracleComp.query a => g a
  | OracleComp.run y s o =>
    let h := fun x => Prod.fst (oracleCompExists (o s x) f)
    let _ := oracleCompDecEq y h (fun _ => inferInstance)
    instDecidableEqProd


end OracleComp

section Fold

def compFold [DecidableEq B] (f : B → A → Comp B) (init : B) (ls : List A) : Comp B :=
  match ls with
    | [] => Comp.pure init
    | a :: ls' => Comp.bind (f init a) (fun x => compFold f x ls')

-- (* Fold a computation over a list *)
-- Fixpoint compFold(A : Type)(B : Set)(eqd : EqDec B)(f : B -> A -> Comp B)(init : B)(ls : list A) :=
--   match ls with
--       | nil => ret init
--       | a :: ls' =>
--         init' <-$ f init a;
--           compFold  _ f init' ls'
--   end.

-- (* foldBody_option is an adapter that allows you to fold a computation with signature B -> A -> Comp (option B) over a list of A, accumulating an option B. *)
-- Definition foldBody_option(A : Type)(B : Set)(eqd : EqDec B)(f : B -> A -> Comp (option B))(b_opt : option B)(a : A) :=
--   match b_opt with
--       | None => ret None
--       | Some b =>
--         f b a
--   end.

end Fold



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
