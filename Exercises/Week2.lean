/-
Proving theorems in Lean: a quick introduction
Yuval Filmus, Shachar Itzhaky, ∧ Jonathan Reicher, 2025
-/

import Mathlib.Tactic


/-
In this file we will learn about more advanced techniques in lean, such as proof
automation, rewriting, induction, and more.
In this file you will learn the following tactics: `exact?`, `rw?`, `apply?`,
`simp`, `linarith`, `induction`.
-/


variable {x y z : ℝ}


lemma proving_with_exact : 0 ≤ x → |x| = x := by
  -- Sometimes, you need to prove something that has probably been proven
  -- before.
  -- Use `exact?` and see what happens!
  exact abs_of_nonneg


lemma rw_1 : ∀ x : ℝ, 0 ≤ x → |x| + |x| = 2 * x := by
  -- Other times, you need to prove something specific. But you can use existing
  -- lemmas for it.
  -- Use the lemma `exact?` found in the previous question to solve this.
  intro x h_gt
  rw [abs_of_nonneg h_gt]
  exact Eq.symm (two_mul x)


def f (x : ℝ) := x + 5


lemma infi : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ (f x - f (x + δ)) < ε := by
  intro ε h_epsilon
  use ε
  constructor
  case left => exact h_epsilon
  case right =>
    unfold f
    linarith

/-
 - split according to sign of a
 - use abs_of_nonneg, abs_of_neg
 - tactics such as linarith and ring could be useful
 -/
lemma infi1_targil1_problem1 {a : ℝ} :
  |a| = |a/2| + |a/2| := by
  by_cases a ≥ 0
  case pos ha =>
    have ha' : a/2 ≥ 0 := by linarith
    rw [absolute_of_nonneg ha, absolute_of]
    simp [abs_of_nonneg ha, abs_of_nonneg ha']
  case neg ha =>
    push_neg at ha
    have ha' : a/2 < 0 := by linarith
    simp [abs_of_neg ha, abs_of_neg ha']
    ring

