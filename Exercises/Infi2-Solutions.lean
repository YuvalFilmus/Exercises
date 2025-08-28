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

lemma infi1_targil2_problem1 : Irrational (Real.sqrt 3) := by
  apply (irrational_iff_ne_rational _).mpr
  intro a b
  by_cases b = 0
  case pos hb =>
    rw [hb]
    push_cast
    rw [div_zero]
    apply sqrt_ne_zero'.mpr
    norm_num
  case neg hb =>
    push_neg at hb
    sorry

lemma infi1_targil2_problem2 {x : ℝ}
  (hnonneg : 0 ≤ x) (hsmall : ∀ ε > 0, x < ε) : x = 0 := by
  cases lt_or_eq_of_le hnonneg
  case inr h => exact h.symm
  case inl h =>
    have := hsmall x h
    have : ¬ (x < x) := irrefl _
    contradiction

lemma infi1_targil2_problem3 {A : Set ℝ}
  (hA : ∃ ε > 0, ∀ a ∈ A, a > ε) : ¬ IsGLB A 0 := by
  obtain ⟨ε, hε⟩ := hA
  unfold IsGLB IsGreatest
  push_neg
  intro h
  simp [upperBounds]
  use ε
  constructor
  · simp [lowerBounds]
    intro a ha
    have := hε.2 a ha
    linarith
  · exact hε.1
