/-
Infi 1 problem sheets
Taken from https://math-wiki.com/index.php/%D7%AA%D7%A8%D7%92%D7%99%D7%9C%D7%99%D7%9D_%D7%9C%D7%A7%D7%95%D7%A8%D7%A1_%D7%90%D7%99%D7%A0%D7%A4%D7%99_1_%D7%AA%D7%A9%D7%A2%D7%90
-/

/-
Sheet 2: https://math-wiki.com/images/f/f2/10Infi1Targil2.pdf
-/

import Mathlib.Tactic
import Mathlib.Data.Real.Irrational

open Real

-- use irrational_iff_ne_rational
lemma infi1_targil2_problem1 : Irrational (Real.sqrt 3) := by
  sorry

lemma infi1_targil2_problem2 {x : ℝ}
  (hnonneg : 0 ≤ x) (hsmall : ∀ ε > 0, x < ε) : x = 0 := by
  sorry

lemma infi1_targil2_problem3 {A : Set ℝ}
  (hA : ∃ ε > 0, ∀ a ∈ A, a > ε) : ¬ IsGLB A 0 := by
  sorry
