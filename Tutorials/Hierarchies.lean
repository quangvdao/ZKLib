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

example [One₁ α] : α := 𝟙

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

class AddCommSemigroup₃ (α : Type) extends AddSemigroup₃ α where
  add_comm : ∀ a b : α, a + b = b + a

@[to_additive AddCommSemigroup₃]
class CommSemigroup₃ (α : Type) extends Semigroup₃ α where
  mul_comm : ∀ a b : α, a * b = b * a

class AddCommMonoid₃ (α : Type) extends AddMonoid₃ α, AddCommSemigroup₃ α

@[to_additive AddCommMonoid₃]
class CommMonoid₃ (α : Type) extends Monoid₃ α, CommSemigroup₃ α

class AddGroup₃ (G : Type) extends AddMonoid₃ G, Neg G where
  neg_add : ∀ a : G, -a + a = 0

@[to_additive AddGroup₃]
class Group₃ (G : Type) extends Monoid₃ G, Inv G where
  inv_mul : ∀ a : G, a⁻¹ * a = 1

attribute [simp] Group₃.inv_mul AddGroup₃.neg_add

@[to_additive]
lemma inv_eq_of_mul [Group₃ G] {a b : G} (h : a * b = 1) : a⁻¹ = b := by
  exact left_inv_eq_right_inv' (Group₃.inv_mul a) h

@[to_additive (attr := simp)]
lemma Group₃.mul_inv {G : Type} [Group₃ G] {a : G} : a * a⁻¹ = 1 := by
  rw [← inv_mul a⁻¹, inv_eq_of_mul (inv_mul a)]

@[to_additive]
lemma mul_left_cancel₃ {G : Type} [Group₃ G] {a b c : G} (h : a * b = a * c) : b = c := by
  rw [← one_mul b, ← one_mul c]
  rw [← Group₃.inv_mul a]
  rw [Semigroup₃.mul_assoc₃, Semigroup₃.mul_assoc₃]
  congr

@[to_additive]
lemma mul_right_cancel₃ {G : Type} [Group₃ G] {a b c : G} (h : b * a = c * a) : b = c := by
  rw [← mul_one b, ← mul_one c, ← Group₃.mul_inv (a := a)]
  rw [← Semigroup₃.mul_assoc₃, ← Semigroup₃.mul_assoc₃]
  congr

class AddCommGroup₃ (G : Type) extends AddGroup₃ G, AddCommMonoid₃ G

@[to_additive AddCommGroup₃]
class CommGroup₃ (G : Type) extends Group₃ G, CommMonoid₃ G


class MulZeroClass (R : Type) extends Mul R, Zero R where
  mul_zero : ∀ a : R, a * 0 = 0
  zero_mul : ∀ a : R, 0 * a = 0

class Ring₃ (R : Type) extends AddGroup₃ R, Monoid₃ R, MulZeroClass R where
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

instance {R : Type} [Ring₃ R] : AddCommGroup₃ R :=
{
  Ring₃.toAddGroup₃ with
  add_comm := by
    intro a b
    have h1 : (1 + 1) * (a + b) = a + (a + b) + b := by
      rw [Ring₃.left_distrib, Ring₃.right_distrib, Ring₃.right_distrib]
      simp
      rw [← add_assoc₃, ← add_assoc₃]
    have h2 : (1 + 1) * (a + b) = a + (b + a) + b := by
      rw [Ring₃.right_distrib, Ring₃.left_distrib]
      simp
      rw [← add_assoc₃, ← add_assoc₃]
    rw [h1] at h2
    sorry
    -- have h3 : (a + b) + b = (b + a) + b := by exact add_left_cancel₃ h1
}

instance {R : Type} [Ring₃ R] : CommMonoid₃ R :=
{
  Ring₃.toMonoid₃ with
  mul_comm := sorry
}


class SMul₃ (α : Type) (β : Type) where
  /-- Scalar multiplication -/
  smul : α → β → β

infixr:73 " • " => SMul₃.smul


class Module₁ (R : Type) [Ring₃ R] (M : Type) [AddCommGroup₃ M] extends SMul₃ R M where
  zero_smul : ∀ m : M, (0 : R) • m = 0
  one_smul : ∀ m : M, (1 : R) • m = m
  mul_smul : ∀ (a b : R) (m : M), (a * b) • m = a • b • m
  add_smul : ∀ (a b : R) (m : M), (a + b) • m = a • m + b • m
  smul_add : ∀ (a : R) (m n : M), a • (m + n) = a • m + a • n



@[ext]
structure MonoidHom₁ (G H : Type) [Monoid₃ G] [Monoid₃ H]  where
  toFun : G → H
  map_one : toFun 1 = 1
  map_mul : ∀ g g', toFun (g * g') = toFun g * toFun g'


instance [Monoid₃ G] [Monoid₃ H] : CoeFun (MonoidHom₁ G H) (fun _ ↦ G → H) where
  coe := MonoidHom₁.toFun

attribute [coe] MonoidHom₁.toFun

example [Monoid₃ G] [Monoid₃ H] (f : MonoidHom₁ G H) : f 1 = 1 := f.map_one


@[ext]
structure AddMonoidHom₁ (G H : Type) [AddMonoid₃ G] [AddMonoid₃ H]  where
  toFun : G → H
  map_zero : toFun 0 = 0
  map_add : ∀ g g', toFun (g + g') = toFun g + toFun g'

instance [AddMonoid₃ G] [AddMonoid₃ H] : CoeFun (AddMonoidHom₁ G H) (fun _ ↦ G → H) where
  coe := AddMonoidHom₁.toFun

attribute [coe] AddMonoidHom₁.toFun

@[ext]
structure RingHom₁ (R S : Type) [Ring₃ R] [Ring₃ S] extends MonoidHom₁ R S, AddMonoidHom₁ R S


class MonoidHomClass₁ (F : Type) (M N : Type) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map_one : ∀ f : F, toFun f 1 = 1
  map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'

def badInst [Monoid M] [Monoid N] [MonoidHomClass₁ F M N] : CoeFun F (fun _ ↦ M → N) where
  coe := MonoidHomClass₁.toFun


class MonoidHomClass₂ (F : Type) (M N : outParam Type) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map_one : ∀ f : F, toFun f 1 = 1
  map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'

instance [Monoid M] [Monoid N] [MonoidHomClass₂ F M N] : CoeFun F (fun _ ↦ M → N) where
  coe := MonoidHomClass₂.toFun

attribute [coe] MonoidHomClass₂.toFun
