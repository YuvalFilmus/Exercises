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
  sorry

/-
 - write a calculational proof (use calc)
 - use abs_suband abs_div
 - tactics such as congr, gcongr, ring, norm_num are useful
 -/
lemma infi1_targil1_problem2 {a x : ℝ}
  (h : |x-a/2| < |a|/2) : |x-a| < |a| := by
  sorry

/-
 - use exact? or apply? to find this lemma in mathlib
 -/
lemma infi1_targil1_problem3 {a b : ℝ} :
  |(|a|-|b|)| ≤ |a-b| := by
  sorry

/-
 - prove this by induction, using a strengthened induction hypothesis
 - use Finset.prod_range_succ to unroll the product
 - use mul_pos_iff and mul_neg_iff to reason about signs
 - use mul_assoc to help with simplification
 - use Nat.cast_le, Nat.cast_lt to lift Nat inequalities to Reals
 - long and challenging exercise!
 -/
lemma infi1_targil1_problem4a {x : ℝ} {n : ℕ} :
  0 < ∏ i ∈ Finset.range (2*n+1), (x - (i + 1)) ↔
  (∃ i < n, 2*i+1 < x ∧ x < 2*i+2) ∨ 2*n+1 < x := by
  sorry

/-
 - split according to sign of various absolute values
 - use appropriate lemmas and tactics to reason about square roots
 - a rather long and challenging exercise!
 -/
lemma infi1_targil1_problem4b {x : ℝ} :
  |2*x^2 - 5*x + 2| < |x+1| ↔ (3 - √7)/2 < x ∧ x < (3 + √7)/2 := by
  sorry

/-
 - split according to sign of various absolute values
 - a rather long exercise!
 -/
lemma infi1_targil1_problem4c {x : ℝ} :
  |(|x+1| - |x-1|)| < 1 ↔ |x| < 1/2 := by
  sorry

/-
 - show instead that 6 * (1^2 + ... + n^2) = n(n+1)(2n+1)/6
 - prove this by induction
 - use Finset.sum_range_succ, mul_add
 - ring and omega could be useful
 -/
lemma infi1_targil1_problem5a {n : ℕ} :
  ∑ i ∈ Finset.range (n+1), i^2 = n*(n+1)*(2*n+1)/6 := by
  sorry

/-
 - use Finset.sum_range_id_mul_two and Nat.eq_of_mul_eq_mul_left
 - employing "cases n" is one way of handling the resulting "n - 1"
 - tricky exercise!
 -/
lemma infi1_targile1_problem5b {n : ℕ} :
  ∑ i ∈ Finset.range n, i^3 = (∑ i ∈ Finset.range n, i)^2 := by
  sorry
