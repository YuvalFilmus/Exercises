/-
Proving theorems in Lean: a quick introduction
Yuval Filmus and Shachar Itzhaky, 2025

Solutions to exercises in Problems.lean.
-/

import Mathlib.Tactic

/-
Proving in Lean:
Working with connectives and quantifiers
-/

section

variable {A B C : Prop}

lemma Axiom1 : A → (B → A) := by
  intro hA _
  exact hA

lemma Axiom2 : (A → (B → C)) → ((A → B) → (A → C)) := by
  intro h₁ h₂ hA
  apply h₁ hA
  apply h₂ hA

lemma Axiom3 : (¬ A → ¬ B) → (B → A) := by
  intro h hB
  contrapose! h
  constructor <;> assumption

lemma XOR_equiv :
  ((A ∧ ¬ B) ∨ (B ∧ ¬ A)) ↔ ((A ∨ B) ∧ (¬ A ∨ ¬ B)) := by
  constructor
  case mp =>
    intro h
    cases h
    case inl h =>
      constructor
      · left; exact h.1
      · right; exact h.2
    case inr h =>
      constructor
      · right; exact h.1
      · left; exact h.2
  case mpr =>
    intro h
    cases h.1
    case inl hA =>
      cases h.2
      case inl hA' => contradiction
      case inr hB' => left; constructor <;> assumption
    case inr hB =>
      cases h.2
      case inl hA' => right; constructor <;> assumption
      case inr hB' => contradiction

end section

lemma nonzero_of_pos {n : ℤ} (hn : n > 0) : n ≠ 0 := by
  contrapose! hn
  subst hn
  rfl

lemma swap_quantifiers {P : ℕ → ℕ → Prop} :
  (∃ x, ∀ y, P x y) → ∀ y, ∃ x, P x y := by
  intro h
  obtain ⟨x, h⟩ := h
  intro y
  use x
  apply h

/-
hint 1: use push_neg to simplify ¬ (...)
hint 2: at the end, try to use omega or aesop
-/
lemma swap_quantifiers_op :
  ∃ P : ℕ → ℕ → Prop,
    ¬ ((∀ y, ∃ x, P x y) → ∃ x, ∀ y, P x y) := by
  use fun x y => x = y
  push_neg
  constructor
  · intro y
    use y
  · intro x
    use x + 1
    omega

lemma aperiodicity_criterion {S : Set ℕ}
  (hrun : ∀ n₀ q, ∃ n ≥ n₀, (∀ i < q, n + i ∈ S) ∧ n + q ∉ S) :
  ¬ ∃ n₀ p, p > 0 ∧ ∀ n ≥ n₀, n ∈ S ↔ n + p ∈ S := by
  by_contra! hper
  -- proof starts here
  obtain ⟨n₀, p, ⟨hp, hper⟩⟩ := hper
  obtain ⟨n, ⟨hn, hrun⟩⟩ := hrun n₀ p
  have hin : n ∈ S := by
    apply hrun.1 0
    exact hp
  have hout : n + p ∉ S := hrun.2
  have := hper n hn
  have := this.mp hin
  contradiction

lemma inverse_of_invertible {f : ℕ → ℕ}
  (inj : ∀ x₁ x₂, f x₁ = f x₂ → x₁ = x₂)
  (surj : ∀ y, ∃ x, f x = y) :
  ∃ g : ℕ → ℕ, (∀ x, f (g x) = x) ∧ (∀ x, g (f x) = x) := by
  choose g hg using surj
  use g
  constructor
  · exact hg
  intro x
  apply inj
  rw [hg]

/-
Proving in Lean:
Common proof strategies
-/
