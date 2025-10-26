/-
Proving theorems in Lean: a quick introduction
Yuval Filmus, Shachar Itzhaky, ∧ Jonathan Reicher, 2025
-/

import Mathlib.Tactic


/-
In this file you will learn how to use Lean, logical connectives, and quantifiers.
This file introduces you to the following symbols: →, ↔, ∧, ∨, ¬, ∀, and ∃
And to the following tactics: `intro`, `exact`, `apply`, `assumption`, `cases`,
`constructor`, `left`, `right` and `contrapose!`.

Everything you need is in the slides, but don't hesitate to ask a question.
https://www.icloud.com/keynote/0f9WShIZaWKcNfbl2QU1-k2JA#Lean2025
Solutions can be found in `SolutionWeek1.lean`.
-/

-- Ignore me, I just define globals
variable {A B C : Prop}


lemma implication_1 : A → (B → A) := by
  sorry

lemma implication_2 : A → (A → B) → B := by
  sorry

lemma implication_3 : (A → (B → C)) → ((A → B) → (A → C)) := by
  sorry

lemma proving_iff : A ↔ A := by
  sorry

lemma using_iff : (A ↔ B) → B → A := by
  sorry

lemma proving_or : A → A ∨ B := by
  sorry

lemma using_or : A ∨ B → B ∨ A := by
  sorry

lemma proving_and : A → (A → B) → A ∧ B := by
  sorry

lemma using_and : A ∧ B → A ∨ B := by
  sorry

-- Let's see if you can use everything you learned so far!
lemma complex : A ∨ (A ∧ B) ↔ A := by
  sorry

lemma using_negation_1 : A → ¬ A → False := by
  sorry

lemma proving_negation_1 : ¬ A → ¬ (A ∧ B) := by
  sorry

lemma proving_negation_2 : (A → B) → (¬ B → ¬ A) := by
  sorry

lemma proving_negation_with_contrapose : (¬ A → ¬ B) → (B → A) := by
  sorry


/-
Good job getting up to this point!
-/


variable {P : ℕ → ℕ → Prop}
variable {Q : ℕ → Prop}


lemma using_forall : (∀ n, P 0 n) → P 0 0 := by
  sorry

lemma proving_forall : (∀ n m, P n m) → (∀ n, P n n) := by
  sorry

lemma proving_exists : (∀ n, Q n) → ∃ n, Q n := by
  sorry

lemma using_exists : ¬ (∃ n, Q n ∧ ¬ Q n) := by
  sorry

lemma swap_quantifiers : (∃ x, ∀ y, P x y) → ∀ y, ∃ x, P x y := by
  sorry

lemma dependent_arrow : (A → B) → (h: A) → B := by
  sorry

lemma proving_functions : ∃ f : ℕ → ℕ, ∀ n, f n = 0 := by
  sorry
  -- Finish this proof with the `rfl` tactic
  -- rfl

variable {X Y Z : Type}

-- Ignore the fact that we use `def` instead of `lemma`
def using_functions : (f : X → Y) → (g : Y → Z) → (X → Z) := by
  sorry

/-
Good job - you finished all the material!
Now, for extra practice, here are some harder questions.
They are completely optional, and they will test your skill.
You may do them in whatever order you feel like.
-/

lemma inverse_of_invertible {f : ℕ → ℕ}
  (inj : ∀ x₁ x₂, f x₁ = f x₂ → x₁ = x₂)
  (surj : ∀ y, ∃ x, f x = y) :
  ∃ g : ℕ → ℕ, (∀ x, f (g x) = x) ∧ (∀ x, g (f x) = x) := by
  sorry

lemma XOR_equiv :
  ((A ∧ ¬ B) ∨ (B ∧ ¬ A)) ↔ ((A ∨ B) ∧ (¬ A ∨ ¬ B)) := by
  sorry


lemma MAJ_equiv :
  ((A ∧ B) ∨ (A ∧ C) ∨ (B ∧ C)) ↔ ((A ∨ B) ∧ (A ∨ C) ∧ (B ∨ C)) := by
  sorry

lemma aperiodicity_criterion {S : Set ℕ}
  (hrun : ∀ n₀ q, ∃ n ≥ n₀, (∀ i < q, n + i ∈ S) ∧ n + q ∉ S) :
  ¬ ∃ n₀ p, p > 0 ∧ ∀ n ≥ n₀, n ∈ S ↔ n + p ∈ S := by
  sorry

