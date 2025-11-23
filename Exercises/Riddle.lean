/-
We are given n numbers arranged in a circle, whose sum is irrational.
Show that there exists a starting point with respect to which all running sums are irrational.
-/

import Mathlib.Tactic
import Mathlib.Logic.Function.Iterate
import Mathlib.Combinatorics.Pigeonhole

open Finset

variable {n : ℕ} [NeZero n]

def sum (v : Fin n → ℝ) : ℝ := ∑ i, v i

def extend (v : Fin n → ℝ) (i : ℕ) : ℝ :=
  v (Fin.ofNat n i)

lemma sum_n_eq_sum (v : Fin n → ℝ) (i : ℕ) :
  ∑ j ∈ Ico i (i + n), extend v j = sum v := by
  induction i
  case zero =>
    simp_rw [sum, zero_add, Nat.Ico_zero_eq_range, sum_range, extend]
    congr! with j hj
    exact Fin.ofNat_val_eq_self j
  case succ i' ih =>
    have : i' + 1 + n = Order.succ (i' + n) := by rw [Order.succ_eq_add_one]; ring
    rw [←ih, this]
    rw [←insert_Ico_add_one_left_eq_Ico (a := i'), sum_insert]
    rw [←insert_Ico_right_eq_Ico_succ (a := i'+1), sum_insert]
    congr 1
    rw [extend, extend]
    congr 1
    rw [Fin.ofNat_eq_cast, Fin.ofNat_eq_cast]
    ext
    rw [Fin.val_natCast, Fin.val_natCast, Nat.add_mod_right]
    · exact right_notMem_Ico
    · gcongr; exact NeZero.one_le
    · rw [mem_Ico]; push_neg; intro h; simp at h
    · nth_rewrite 1 [←add_zero i']; gcongr; exact NeZero.one_le

lemma sum_k_mul_n_eq_k_mul_sum (v : Fin n → ℝ) (i k : ℕ) :
  ∑ j ∈ Ico i (i + k*n), extend v j = k * sum v := by
  induction k
  case zero => simp
  case succ k' ih =>
    have : Ico i (i + (k' + 1) * n) = (Ico i (i + k' * n)) ∪ Ico (i + k' * n) (i + (k' + 1) * n) := by
      rw [Ico_union_Ico_eq_Ico]
      · omega
      · rw [add_mul]; omega
    rw [this]
    have : i + (k' + 1) * n = i + k' * n + n := by ring
    rw [this]
    have : Disjoint (Ico i (i + k' * n)) (Ico (i + k' * n) (i + k' * n + n)) := by
      apply Ico_disjoint_Ico_consecutive
    rw [sum_union this, ih, sum_n_eq_sum]
    push_cast
    ring

theorem main (v : Fin n → ℝ) (hsum : Irrational (sum v)) :
  ∃ i, ∀ j > i, Irrational (∑ k ∈ Ico i j, extend v k) := by
  by_contra!
  choose j hj using this
  let x t := j^[t] 0
  have xsucc {t} : x (t + 1) = j (x t) := by
    unfold x
    rw [add_comm, Function.iterate_add_apply, Function.iterate_one]
  have xmon : StrictMono x := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [xsucc]
    exact (hj _).1
  have : (Set.range x).Infinite := by
    apply Set.infinite_range_of_injective
    exact StrictMono.injective xmon
  obtain ⟨i₁, hi₁, i₂, hi₂, i_lt, i_mod⟩ := Nat.exists_lt_modEq_of_infinite this (Nat.pos_of_neZero n)
  have : ∃ k > 0, i₂ = i₁ + k * n := by
    have : i₁ ≡ i₂ [ZMOD n] := by exact Int.natCast_modEq_iff.mpr i_mod
    obtain ⟨k, hk⟩ := Int.modEq_iff_add_fac.mp this
    have kpos : k > 0 := by
      have t_lt_ℤ : (i₂ : ℤ) > i₁ := by exact Int.ofNat_lt.mpr i_lt
      contrapose! t_lt_ℤ
      rw [hk]
      have : n * k ≤ 0 := by
        apply Int.mul_nonpos_of_nonneg_of_nonpos ?_ t_lt_ℤ
        exact Int.natCast_nonneg n
      exact (add_le_iff_nonpos_right ↑i₁).mpr this
    use k.toNat
    constructor
    · exact Int.pos_iff_toNat_pos.mp kpos
    · zify
      rw [hk, mul_comm]
      congr
      apply Int.eq_natCast_toNat.mpr
      exact Int.le_of_lt kpos
  obtain ⟨k, kpos, i₂_eq⟩ := this
  have : ¬ Irrational (∑ l ∈ Ico i₁ i₂, extend v l) := by
    obtain ⟨t₁, ht₁⟩ := Set.mem_range.mpr hi₁
    obtain ⟨t₂, ht₂⟩ := Set.mem_range.mpr hi₂
    rw [←ht₁, ←ht₂]
    rw [←ht₁, ←ht₂] at i_lt
    have h_lt : t₁ < t₂ := (StrictMono.lt_iff_lt xmon).mp i_lt
    have h_le : t₁+1 ≤ t₂ := h_lt
    clear ht₂
    induction t₂, h_le using Nat.le_induction
    case base =>
      rw [xsucc]
      exact (hj _).2
    case succ _ t₂' ht₂' ih =>
      have hunion : Ico (x t₁) (x (t₂' + 1)) = Ico (x t₁) (x t₂') ∪ Ico (x t₂') (x (t₂' + 1)) := by
        rw [Ico_union_Ico_eq_Ico]
        · apply (StrictMono.le_iff_le xmon).mpr
          exact Nat.le_of_lt_succ h_lt
        · apply (StrictMono.le_iff_le xmon).mpr
          exact Nat.le_add_right t₂' 1
      have hdisj : Disjoint (Ico (x t₁) (x t₂')) (Ico (x t₂') (x (t₂' + 1))) := by
        exact Ico_disjoint_Ico_consecutive (x t₁) (x t₂') (x (t₂' + 1))
      rw [hunion, sum_union hdisj]
      have irr₁ : ¬ Irrational (∑ x ∈ Ico (x t₁) (x t₂'), extend v x) := by
        apply ih
        · exact (StrictMono.lt_iff_lt xmon).mpr ht₂'
        · exact ht₂'
      have irr₂ : ¬ Irrational (∑ x ∈ Ico (x t₂') (x (t₂' + 1)), extend v x) := by
        rw [xsucc]
        exact (hj _).2
      by_contra!
      cases this.add_cases <;> contradiction
  rw [i₂_eq, sum_k_mul_n_eq_k_mul_sum] at this
  have : Irrational (k * sum v) := by
    apply Irrational.natCast_mul hsum
    exact Nat.ne_zero_of_lt kpos
  contradiction
