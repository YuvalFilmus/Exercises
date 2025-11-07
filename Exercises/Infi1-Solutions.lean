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
 - use abs_sub and abs_div
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
  -- strengthen induction hypothesis
  suffices
    (0 < ∏ i ∈ Finset.range (2*n+1), (x - (i + 1)) ↔
     (∃ i < n, 2*i+1 < x ∧ x < 2*i+2) ∨ 2*n+1 < x) ∧
    (∏ i ∈ Finset.range (2*n+1), (x - (i + 1)) < 0 ↔
     (∃ i < n, 2*i+2 < x ∧ x < 2*i+3) ∨ x < 1) by
    exact this.1
  induction n
  case zero =>
    simp
  case succ n ih =>
    have : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by ring
    rw [this]
    rw [Finset.prod_range_succ, Finset.prod_range_succ, mul_assoc]
    have hpos :
      0 < (x - (↑(2 * n + 1) + 1)) * (x - (↑(2 * n + 2) + 1)) ↔
      x < 2 * n + 2 ∨ 2 * n + 3 < x := by
      rw [mul_pos_iff]
      constructor
      · intro h
        cases h
        case _ h =>
          obtain ⟨h₁, h₂⟩ := h
          simp at h₁ h₂
          right
          linarith
        case _ h =>
          obtain ⟨h₁, h₂⟩ := h
          simp at h₁ h₂
          left
          linarith
      · intro h
        cases h
        case _ h =>
          right
          constructor
          · simp; linarith
          · simp; linarith
        case _ h =>
          left
          constructor
          · simp; linarith
          · simp; linarith
    have hneg :
      (x - (↑(2 * n + 1) + 1)) * (x - (↑(2 * n + 2) + 1)) < 0 ↔
      2 * n + 2 < x ∧ x < 2 * n + 3 := by
      rw [mul_neg_iff]
      constructor
      · intro h
        cases h
        case _ h =>
          obtain ⟨h₁, h₂⟩ := h
          simp at h₁ h₂
          constructor <;> linarith
        case _ h =>
          obtain ⟨h₁, h₂⟩ := h
          simp at h₁ h₂
          linarith
      · intro h
        obtain ⟨h₁, h₂⟩ := h
        left
        constructor <;> (simp; linarith)
    constructor
    · rw [mul_pos_iff, ih.1, ih.2]
      constructor
      · intro h
        cases h
        case _ h =>
          obtain ⟨h₁, h₂⟩ := h
          cases h₁
          case _ h₁ =>
            obtain ⟨i, hi₁, hi₂, hi₃⟩ := h₁
            left
            use i
            constructor; linarith; constructor <;> linarith
          case _ h₁ =>
            rw [hpos] at h₂
            cases h₂
            case _ h₂ =>
              left
              use n
              constructor; linarith; constructor <;> linarith
            case _ h₂ =>
              right
              simp [mul_add]
              linarith
        case _ h =>
          obtain ⟨h₁, h₂⟩ := h
          exfalso
          rw [hneg] at h₂
          have := h₂.1
          cases h₁
          case _ h₁ =>
            obtain ⟨i, hi₁, hi₂, hi₃⟩ := h₁
            have : i+1 ≤ n := by omega
            have : ↑(i+1) ≤ (n : ℝ) := Nat.cast_le.mpr this
            simp at this
            linarith
          case _ h₁ =>
            linarith
      · intro h
        cases h
        case _ h =>
          obtain ⟨i, hi₁, hi₂, hi₃⟩ := h
          have : i ≤ n := by omega
          by_cases i = n
          case pos hi₁ =>
            left
            constructor
            · right
              rwa [←hi₁]
            · rw [hpos]
              left
              rwa [←hi₁]
          case neg hi₁ =>
            push_neg at hi₁
            have : i < n := by omega
            left
            constructor
            · left
              use i
            · rw [hpos]
              left
              have : (i:ℝ) < (n:ℝ) := by
                apply Nat.cast_lt.mpr
                assumption
              linarith
        case _ h =>
          simp [mul_add] at h
          left
          constructor
          · right
            linarith
          · rw [hpos]
            right
            linarith
    · rw [mul_neg_iff, ih.1, ih.2]
      constructor
      · intro h
        cases h
        case _ h =>
          obtain ⟨h₁, h₂⟩ := h
          rw [hneg] at h₂
          left
          use n
          constructor; omega; assumption
        case _ h =>
          obtain ⟨h₁, h₂⟩ := h
          rw [hpos] at h₂
          cases h₁
          case _ h₁ =>
            obtain ⟨i, hi₁, hi₂⟩ := h₁
            left
            use i
            constructor; omega; assumption
          case _ h₁ =>
            right
            assumption
      · intro h
        cases h
        case _ h =>
          obtain ⟨i, hi₁, hi₂, hi₃⟩ := h
          by_cases i = n
          case pos hi₁ =>
            left
            constructor
            · right
              rw [←hi₁]
              linarith
            · rw [hneg]
              constructor
              · rwa [←hi₁]
              · rwa [←hi₁]
          case neg hi₁ =>
            push_neg at hi₁
            have : i < n := by omega
            right
            constructor
            · left
              use i
            · rw [hpos]
              left
              have : i+1 ≤ n := by omega
              have : ↑(i+1) ≤ (n : ℝ) := Nat.cast_le.mpr this
              simp at this
              linarith
        case _ h =>
          right
          constructor
          · right; assumption
          · rw [hpos]
            left
            linarith

/-
 - split according to sign of various absolute values
 - use appropriate lemmas and tactics to reason about square roots
 - a rather long and challenging exercise!
 -/
lemma infi1_targil1_problem4b {x : ℝ} :
  |2*x^2 - 5*x + 2| < |x+1| ↔ (3 - √7)/2 < x ∧ x < (3 + √7)/2 := by
  have : 2 < √7 := by
    apply (Real.lt_sqrt ?_).mpr
    repeat norm_num
  have : √7 < 3 := by
    apply (Real.sqrt_lt' ?_).mpr
    repeat norm_num
  have h : 2*x^2 - 6*x + 1 = 2 * (x - (3-√7)/2) * (x - (3+√7)/2) := by
    ring_nf
    simp [Real.sqrt_sq]
    ring
  have ineq : 0 < -(2 * (x - (3 - √7) / 2) * (x - (3 + √7) / 2)) ↔ (3 - √7) / 2 < x ∧ x < (3 + √7) / 2 := by
    rw [lt_neg, neg_zero]
    have : (0 : ℝ) = 2 * 0 := by simp
    rw [this, mul_assoc, mul_lt_mul_iff_of_pos_left]
    rw [mul_neg_iff]
    constructor
    · intro h
      cases h
      case mp.inl h =>
        obtain ⟨h₁, h₂⟩ := h
        constructor <;> linarith
      case mp.inr h =>
        obtain ⟨h₁, h₂⟩ := h
        linarith
    · intro ⟨h₁, h₂⟩
      left
      constructor <;> linarith
    norm_num
  have : 2*x^2 - 5*x + 2 = 2 * (x - 2) * (x - 1/2) := by ring
  rw [this]
  rw [abs_mul, abs_mul]
  norm_num
  by_cases x < -1
  case pos =>
    rw [abs_of_neg (a := x+1), abs_of_neg (a := x-1/2), abs_of_neg (a := x-2)]
    have : x ≤ (3 - √7)/2 := by linarith
    have : ¬ (3 - √7)/2 < x := by linarith
    simp [this]
    apply le_of_sub_nonneg
    have : 0 ≤ (x-1)^2 := by apply sq_nonneg
    have : 0 ≤ 2*(x-1)^2+1 := by linarith
    convert this using 1
    ring
    repeat linarith
  case neg =>
  by_cases x < 1/2
  case pos =>
    rw [abs_of_nonneg (a := x+1), abs_of_neg (a := x-1/2), abs_of_neg (a := x-2)]
    rw [←sub_pos]
    have : x + 1 - 2 * -(x - 2) * -(x - 1 / 2) = -(2*x^2 - 6*x + 1) := by ring
    rw [this, h]
    exact ineq
    repeat linarith
  case neg =>
  by_cases x < 2
  case pos =>
    rw [abs_of_nonneg (a := x+1), abs_of_nonneg (a := x-1/2), abs_of_neg (a := x-2)]
    have : (3 - √7)/2 < x := by linarith
    simp [this]
    have : x < (3 + √7)/2 := by linarith
    simp [this]
    apply lt_of_sub_pos
    have : 0 ≤ (x-1)^2 := by apply sq_nonneg
    have : 0 < 2*(x-1)^2+1 := by linarith
    convert this using 1
    ring
    repeat linarith
  case neg =>
    rw [abs_of_nonneg (a := x+1), abs_of_nonneg (a := x-1/2), abs_of_nonneg (a := x-2)]
    rw [←sub_pos]
    have : x + 1 - 2 * (x - 2) * (x - 1 / 2) = -(2*x^2 - 6*x + 1) := by ring
    rw [this, h]
    exact ineq
    repeat linarith

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
