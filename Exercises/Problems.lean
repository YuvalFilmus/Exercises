/-
Proving theorems in Lean: a quick introduction
Yuval Filmus and Shachar Itzhaky, 2025

Exercises on the material presented in the slides.
Full solutions can be found in Solutions.lean.
Every exercise can have more than one solution!
-/

import Mathlib.Tactic

/-
Proving in Lean:
Working with connectives and quantifiers
-/

section

variable {A B C : Prop}

lemma Axiom1 : A → (B → A) := by
  sorry

lemma Axiom2 : (A → (B → C)) → ((A → B) → (A → C)) := by
  sorry

lemma Axiom3 : (¬ A → ¬ B) → (B → A) := by
  sorry

lemma XOR_equiv :
  ((A ∧ ¬ B) ∨ (B ∧ ¬ A)) ↔ ((A ∨ B) ∧ (¬ A ∨ ¬ B)) := by
  sorry

end section

lemma nonzero_of_pos {n : ℤ} (hn : n > 0) : n ≠ 0 := by
  sorry

lemma swap_quantifiers {P : ℕ → ℕ → Prop} :
  (∃ x, ∀ y, P x y) → ∀ y, ∃ x, P x y := by
  sorry

/-
hint 1: use push_neg to simplify ¬ (...)
hint 2: at the end, try to use omega or aesop
-/
lemma swap_quantifiers_op :
  ∃ P : ℕ → ℕ → Prop,
    ¬ ((∀ y, ∃ x, P x y) → ∃ x, ∀ y, P x y) := by
  sorry

lemma aperiodicity_criterion {S : Set ℕ}
  (hrun : ∀ n₀ q, ∃ n ≥ n₀, (∀ i < q, n + i ∈ S) ∧ n + q ∉ S) :
  ¬ ∃ n₀ p, p > 0 ∧ ∀ n ≥ n₀, n ∈ S ↔ n + p ∈ S := by
  by_contra! hper
  sorry

lemma inverse_of_invertible {f : ℕ → ℕ}
  (inj : ∀ x₁ x₂, f x₁ = f x₂ → x₁ = x₂)
  (surj : ∀ y, ∃ x, f x = y) :
  ∃ g : ℕ → ℕ, (∀ x, f (g x) = x) ∧ (∀ x, g (f x) = x) := by
  sorry

/-
Proving in Lean:
Common proof strategies
-/
