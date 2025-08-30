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
    set g := Int.gcd a b with hg
    set a' := a/g with ha'
    set b' := b/g with hb'
    have hab' : Int.gcd a' b' = 1 := by
      rw [ha', hb', hg]
      rwa [Int.gcd_ediv_gcd_ediv_gcd_of_ne_zero_right]
    suffices Real.sqrt 3 ≠ a'/b' by
      contrapose! this
      rw [ha', hb', this]
      rw [Int.cast_div, Int.cast_div]
      rw [div_div_div_cancel_right₀ (by aesop)]
      · exact Int.gcd_dvd_right a b
      · aesop
      · exact Int.gcd_dvd_left a b
      · aesop
    by_contra! h
    have : 3 * (b')^2 = (a')^2 := by
      have : √3 * √3 = (a' / b') * (a' / b') := by rw [h]
      rw [←sq, sq_sqrt (by norm_num)] at this
      rify
      rw [this, sq, sq]
      have : (b' : ℝ) ≠ 0 := by aesop
      field_simp
    have ha3 : 3 ∣ a' := by
      apply Prime.dvd_of_dvd_pow (by norm_num)
      exact Dvd.intro (b'^2) this
    have hb3 : 3 ∣ b' := by
      apply Prime.dvd_of_dvd_pow (by norm_num)
      obtain ⟨c, hc⟩ := dvd_def.mp ha3
      rw [hc] at this
      apply Dvd.intro (c^2)
      suffices 3 * (3 * c^2) = 3 * (b')^2 by
        apply Int.eq_of_mul_eq_mul_left (show 3 ≠ 0 by norm_num)
        assumption
      rw [this]
      ring
    have : 3 ∣ Int.gcd a' b' := Int.dvd_gcd ha3 hb3
    rw [hab'] at this
    norm_num at this

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
