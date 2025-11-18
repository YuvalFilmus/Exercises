import Mathlib.Tactic

open Classical

-- Mathlib: LinearOrder
class TotalOrder (α : Type*) where
  le : α → α → Prop
  le_refl a : le a a
  le_trans {a b c} : le a b → le b c → le a c
  le_antisymm {a b} : le a b → le b a → a = b
  le_total a b : le a b ∨ le b a

-- Mathlib: ≤
notation x " ≲ " y => TotalOrder.le x y

-- Mathlib: max
noncomputable def maximum {α} [TotalOrder α] (x y : α) :=
  if x ≲ y then y else x

-- Mathlib: le_max
lemma le_maximum {α} [TotalOrder α] {x y z : α} :
  (x ≲ maximum y z) ↔ (x ≲ y) ∨ (x ≲ z) := by
  unfold maximum
  constructor
  case mp => split <;> tauto
  case mpr =>
    rintro (h|h) -- combination of intro and cases
    case inl =>
      split
      case isTrue h' => exact TotalOrder.le_trans h h'
      case isFalse _ => exact h
    case inr =>
      split
      case isTrue _ => exact h
      case isFalse h' =>
        have := TotalOrder.le_total y z
        replace h' : z ≲ y := by tauto
        exact TotalOrder.le_trans h h'

instance : TotalOrder ℕ where
  le a b := ∃ x, b = a + x
  le_refl a := by use 0; omega
  le_trans {a b c} := by
    rintro ⟨x, hab⟩ ⟨y, hbc⟩
    use x + y; omega
  le_antisymm hab hba := by omega
  le_total a b := by
    by_cases a ≤ b
    case pos h => left;  use b - a; omega
    case neg h => right; use a - b; omega

instance {α : Type*} {x : α} : TotalOrder ({x} : Set α) where
  le a b := True
  le_refl a := by simp
  le_trans hab hbc := by simp
  le_antisymm {a b} hab hba := by aesop
  le_total a b := by simp

instance opposite {α : Type*} [TotalOrder α] : TotalOrder α where
  le a b := b ≲ a
  le_refl a := TotalOrder.le_refl a
  le_trans hab hbc := TotalOrder.le_trans hbc hab
  le_antisymm hab hba := TotalOrder.le_antisymm hba hab
  le_total a b := TotalOrder.le_total b a

noncomputable def minimum {α : Type*} [inst : TotalOrder α] {x y : α} :=
  @maximum α (@opposite α inst) x y

example {α} [TotalOrder α] [Inhabited α] [DecidableEq α] (S : Finset α) :
  ∃ bnd, ∀ x ∈ S, x ≲ bnd := by
  induction S using Finset.induction_on
  case empty =>
    use Inhabited.default -- an arbitrary element of α
    intro x hx
    simp at hx
  case insert a T ha ih =>
    obtain ⟨bnd, ih⟩ := ih
    cases TotalOrder.le_total bnd a
    case inl h => -- bnd ≲ a
      use a
      intro x hx
      cases Finset.mem_insert.mp hx
      case inl hx => subst hx; exact TotalOrder.le_refl x
      case inr hx => exact TotalOrder.le_trans (ih x hx) h
    case inr h => -- a ≲ bnd
      use bnd
      intro x hx
      cases Finset.mem_insert.mp hx
      case inl hx => subst hx; exact h
      case inr hx => exact ih x hx
