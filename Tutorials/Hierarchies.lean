import Mathlib.Algebra.Group.Basic

class One₁ (α : Type) where
  one : α

#check One₁.one

example (α : Type) [One₁ α] : α := One₁.one

@[class] structure One₂ (α : Type) where
  one : α

#check One₂.one

example (α : Type) [s :One₂ α] : α := One₂.one s

notation "𝟙" => One₁.one

example {a : Type} [One₁ α] : α := 𝟙

class Dia₁ (α : Type) where
  dia : α → α → α

infixl:70 " ⬝ " => Dia₁.dia

class Semigroup₁ (α : Type) where
  toDia₁ : Dia₁ α
  dia_assoc : ∀ a b c : α, a ⬝ b ⬝ c = a ⬝ (b ⬝ c)

example {α : Type} [Dia₁ α] [Semigroup₁ α] (a b : α) : α := a ⬝ b

attribute [instance] Semigroup₁.toDia₁

example {α : Type} [Semigroup₁ α] (a b : α) : α := a ⬝ b

class Semigroup₂ (α : Type) extends Dia₁ α where
  dia_assoc : ∀ a b c : α, a ⬝ b ⬝ c = a ⬝ (b ⬝ c)

example {α : Type} [Semigroup₂ α] (a b : α) : α := a ⬝ b

class DiaOneClass₁ (α : Type) extends One₁ α, Dia₁ α where
  one_dia : ∀ a : α, 𝟙 ⬝ a = a
  dia_one : ∀ a : α, a ⬝ 𝟙 = a

set_option trace.Meta.synthInstance true in
example {α : Type} [DiaOneClass₁ α] (a b : α) : Prop := a ⬝ b = 𝟙


class Monoid₁ (α : Type) extends Semigroup₁ α, DiaOneClass₁ α


example {α : Type} [Monoid₁ α] :
  (Monoid₁.toSemigroup₁.toDia₁.dia : α → α → α) = Monoid₁.toDiaOneClass₁.toDia₁.dia := rfl

-- This runs into the problem of having two separate `Dia₁` instances
class Monoid₂ (α : Type) where
  toSemigroup₁ : Semigroup₁ α
  toDiaOneClass₁ : DiaOneClass₁ α

-- This extension equality also works for structures

/-
Monoid₁.mk {α : Type} [toSemigroup₁ : Semigroup₁ α] [toOne₁ : One₁ α] (one_dia : ∀ (a : α), 𝟙 ⬝ a = a)
  (dia_one : ∀ (a : α), a ⬝ 𝟙 = a) : Monoid₁ α

Note: the DiaOneClass₁ instance is torn apart to have compatible Dia₁ instance with Semigroup₁
-/
#check Monoid₁.mk

#check Monoid₁.toSemigroup₁
#check Monoid₁.toDiaOneClass₁


class Inv₁ (α : Type) where
  /-- The inversion function -/
  inv : α → α

@[inherit_doc]
postfix:max "⁻¹" => Inv₁.inv

class Group₁ (G : Type) extends Monoid₁ G, Inv₁ G where
  inv_dia : ∀ (a : G), a⁻¹ ⬝ a = 𝟙

-- This makes it easier to invoke these properties to prove theorems
export DiaOneClass₁ (one_dia dia_one)
export Semigroup₁ (dia_assoc)
export Group₁ (inv_dia)

theorem left_inv_eq_right_inv₁ {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⬝ a = 𝟙) (hac : a ⬝ c = 𝟙) : b = c :=
  calc
    b = b ⬝ 𝟙 := by rw [dia_one]
    _ = b ⬝ (a ⬝ c) := by rw [hac]
    _ = b ⬝ a ⬝ c := by rw [dia_assoc]
    _ = 𝟙 ⬝ c := by rw [hba]
    _ = c := by rw [one_dia]

-- more succinct proof may be possible if I tag everything with simp or aesop

theorem inv_eq_of_dia [Group₁ G] {a b : G} (h : a ⬝ b = 𝟙) : a⁻¹ = b := by
  exact left_inv_eq_right_inv₁ (inv_dia a) h

theorem dia_inv [Group₁ G] (a : G) : a ⬝ a⁻¹ = 𝟙 := by
  rw [← inv_dia a⁻¹, inv_eq_of_dia (inv_dia a)]

class AddSemigroup₃ (α : Type) extends Add α where
/-- Addition is associative -/
  add_assoc₃ : ∀ a b c : α, a + b + c = a + (b + c)

@[to_additive AddSemigroup₃]
class Semigroup₃ (α : Type) extends Mul α where
/-- Multiplication is associative -/
  mul_assoc₃ : ∀ a b c : α, a * b * c = a * (b * c)

class AddMonoid₃ (α : Type) extends AddSemigroup₃ α, AddZeroClass α

@[to_additive AddMonoid₃]
class Monoid₃ (α : Type) extends Semigroup₃ α, MulOneClass α

attribute [to_additive existing] Monoid₃.toMulOneClass

export Semigroup₃ (mul_assoc₃)
export AddSemigroup₃ (add_assoc₃)

@[to_additive]
lemma left_inv_eq_right_inv' {M : Type} [Monoid₃ M] {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mul c, ← hba, mul_assoc₃, hac, mul_one b]

#check left_neg_eq_right_neg'
