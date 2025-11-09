/-
Proving theorems in Lean: a quick introduction
Yuval Filmus, Shachar Itzhaky, ∧ Jonathan Reicher, 2025
-/

import Mathlib.Tactic


/-
Hello, young Lean user.

In this file you will learn about more advanced techniques in lean, such as proof
automation, rewriting, induction, and more. You will learn the following tactics:
`exact?`, `rw?`, `apply?`, `simp`, `linarith`, `induction` and `by_cases`.
-/


variable {A B C : Prop}
variable {x y z : ℝ}


lemma warm_up : (A ∨ B → C) → (¬A → B) → (A ∨ ¬A) → C := by
  sorry


lemma proving_with_exact : 0 ≤ x → |x| = x := by
  -- Sometimes, you need to prove something that has probably been proven
  -- before.
  -- Use `exact?` and see what happens!
  sorry


lemma rewriting_with_rw : ∀ x : ℝ, 0 ≤ x → |x| + |x| = 2 * x := by
  -- Other times, you need to prove something specific. But you can use existing
  -- lemmas for it.
  -- Use the lemma `exact?` found in the previous question to solve this.
  sorry


lemma branching_by_cases : (¬A → B) → A ∨ B := by
  sorry


lemma proving_if : if 0 < x then |x| = x else |x| = -x := by
  sorry


lemma proof_by_induction (n : ℕ) : ∃ k, 2 * k + 1 = n ∨ 2 * k = n := by
  sorry


def f (x : ℝ) := x + 5


lemma using_unfold : f (10 + x) = 10 + f (x) := by
  sorry


lemma infi : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ (f x - f (x + δ)) < ε := by
  sorry


lemma lets_learn_about_simp (x : List ℝ) (h : x = [10, 20, 30])
: (x ++ [40, 50]).length = 5 := by
  sorry


/-
 - split according to sign of a
 - use abs_of_nonneg, abs_of_neg
 - tactics such as linarith and ring could be useful
 -/
lemma absolute_fun {a : ℝ} :
  |a| = |a/2| + |a/2| := by
  sorry


/-
A certificate is a set of indices that are enough to show the output of `f` for
a given input `y`.

This lemma shows that a certificate `S` must be non-empty.
-/
lemma cert_nontriv
  {f : (ℕ → Bool) → Bool}
  (h₁ : ∃ x, f x = true)
  (h₂ : ∃ x, f x = false)
  {x : ℕ → Bool}
  {S : Set ℕ}
  (h_certificate : ∀ y : ℕ → Bool, (∀ n ∈ S, y n = x n) → f y = f x)
  : ∃ n, n ∈ S := by
  /-
  HINT:
  Start by using proof by contradiction (Assume goal is wrong and prove `False`).
  For that, show `f x = true` and `f x = false` (use forward reasoning).
  -/
  sorry


/-- A function is periodic (like sin or cos) -/
def has_period (f : ℕ → ℕ) (r : ℕ) :=
  ∀ n, f (n + r) = f n


lemma periodicity {f r} (hf : has_period f r) : ∀ m, has_period f (m*r) := by
  sorry


def array_max (array : Array ℝ) (upTo : ℕ) (h : array.size > 0) :=
  if _ : array.size <= upTo then
    array[array.size - 1]
  else if _ : upTo = 0 then
    array[upTo]
  else
    max array[upTo] (array_max array (upTo - 1) h)


-- Challenge question: For those who are not afraid.
-- (This next question is optional)


lemma array_max_of_all_equal
  (a : Array ℝ)
  (upTo : ℕ)
  (h₁ : ∀ x ∈ a, ∀ y ∈ a, x = y)
  (h₂ : a.size > 0)
  : ∀ x ∈ a, x = array_max a upTo h₂ := by
  sorry

