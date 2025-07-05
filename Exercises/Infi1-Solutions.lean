/-
Infi 1 problem sheets
Taken from https://math-wiki.com/index.php/%D7%AA%D7%A8%D7%92%D7%99%D7%9C%D7%99%D7%9D_%D7%9C%D7%A7%D7%95%D7%A8%D7%A1_%D7%90%D7%99%D7%A0%D7%A4%D7%99_1_%D7%AA%D7%A9%D7%A2%D7%90
-/

/-
Sheet 1: https://math-wiki.com/images/1/18/10Infi1Targil1.pdf
-/

import Mathlib.Tactic

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
    simp [abs_of_nonneg ha, abs_of_nonneg ha']
  case neg ha =>
    push_neg at ha
    have ha' : a/2 < 0 := by linarith
    simp [abs_of_neg ha, abs_of_neg ha']
    ring

/-
 - write a calculational proof (use calc)
 - use abs_suband abs_div
 - tactics such as congr, gcongr, ring, norm_num are useful
 -/
lemma infi1_targil1_problem2 {a x : ℝ}
  (h : |x-a/2| < |a|/2) : |x-a| < |a| := by
  calc
    |x-a| = |x-a/2-a/2| := by
      congr 1
      ring
    _ ≤ |x-a/2| + |a/2| := by
      apply abs_sub
    _ < |a|/2 + |a/2| := by
      gcongr
    _ = |a|/2 + |a|/2 := by
      congr
      rw [abs_div]
      norm_num
    _ = |a| := by
      ring

/-
 - use exact? or apply? to find this lemma in mathlib
 -/
lemma infi1_targil1_problem3 {a b : ℝ} :
  |(|a|-|b|)| ≤ |a-b| := by
  exact abs_abs_sub_abs_le a b

/-
 - TODO: parts a and b
 -/

/-
 - split according to sign of various absolute values
 - a rather long exercise!
 -/
lemma infi1_targil1_problem4c {x : ℝ} :
  |(|x+1| - |x-1|)| < 1 ↔ |x| < 1/2 := by
  by_cases x < -1
  case pos =>
    rw [abs_of_neg (a := x+1), abs_of_neg (a := x), abs_of_neg (a := x-1)]
    ring_nf
    simp
    repeat linarith
  case neg =>
  by_cases x < 0
  case pos =>
    rw [abs_of_nonneg (a := x+1), abs_of_neg (a := x), abs_of_neg (a := x-1)]
    ring_nf
    rw [abs_mul]
    norm_num
    rw [abs_of_neg (a := x)]
    symm
    apply lt_div_iff₀
    simp
    repeat linarith
  case neg =>
  by_cases x < 1
  case pos =>
    rw [abs_of_nonneg (a := x+1), abs_of_nonneg (a := x), abs_of_neg (a := x-1)]
    ring_nf
    rw [abs_mul]
    norm_num
    rw [abs_of_nonneg (a := x)]
    symm
    apply lt_div_iff₀
    simp
    repeat linarith
  case neg =>
    rw [abs_of_nonneg (a := x+1), abs_of_nonneg (a := x), abs_of_nonneg (a := x-1)]
    ring_nf
    simp
    repeat linarith

/-
 - show instead that 6 * (1^2 + ... + n^2) = n(n+1)(2n+1)/6
 - prove this by induction
 - use Finset.sum_range_succ, mul_add
 - ring and omega could be useful
 -/
lemma infi1_targil1_problem5a {n : ℕ} :
  ∑ i ∈ Finset.range (n+1), i^2 = n*(n+1)*(2*n+1)/6 := by
  suffices 6 * ∑ i ∈ Finset.range (n+1), i^2 = n*(n+1)*(2*n+1) by
    omega
  induction n
  case zero =>
    simp
  case succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

/-
 - use Finset.sum_range_id_mul_two and Nat.eq_of_mul_eq_mul_left
 - employing "cases n" is one way of handling the resulting "n - 1"
 - tricky exercise!
 -/
lemma infi1_targile1_problem5b {n : ℕ} :
  ∑ i ∈ Finset.range n, i^3 = (∑ i ∈ Finset.range n, i)^2 := by
  suffices h : 4 * ∑ i ∈ Finset.range n, i^3 = ((∑ i ∈ Finset.range n, i) * 2)^2 by
    have : ((∑ i ∈ Finset.range n, i) * 2)^2 = 4 * (∑ i ∈ Finset.range n, i)^2 := by
      ring
    rw [this] at h
    apply Nat.eq_of_mul_eq_mul_left (n := 4)
    · simp
    exact h
  rw [Finset.sum_range_id_mul_two]
  cases n
  case zero =>
    simp
  case succ n =>
    simp
    induction n
    case zero =>
      simp
    case succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      ring
