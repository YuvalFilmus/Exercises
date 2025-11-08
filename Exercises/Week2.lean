/-
Proving theorems in Lean: a quick introduction
Yuval Filmus, Shachar Itzhaky, ∧ Jonathan Reicher, 2025
-/

import Mathlib.Tactic


/-
In this file we will learn about more advanced techniques in lean, such as proof
automation, rewriting, induction, and more.
In this file you will learn the following tactics: `exact?`, `rw?`, `apply?`,
`simp`, `linarith`, `induction` and `by_cases`.
-/


variable {A B C : Prop}
variable {x y z : ℝ}


lemma warm_up : (A ∨ B → C) → (¬A → B) → (A ∨ ¬A) → C := by
  intros h1 h2 h3
  -- We use the first implication to create C
  apply h1
  -- Now need to prove A ∨ B
  cases h3
  case inl h_A =>
    left
    exact h_A
  case inr h_not_A =>
    right
    apply h2
    exact h_not_A


lemma proving_with_exact : 0 ≤ x → |x| = x := by
  -- Sometimes, you need to prove something that has probably been proven
  -- before.
  -- Use `exact?` and see what happens!
  exact abs_of_nonneg


lemma rewriting_with_rw : ∀ x : ℝ, 0 ≤ x → |x| + |x| = 2 * x := by
  -- Other times, you need to prove something specific. But you can use existing
  -- lemmas for it.
  -- Use the lemma `exact?` found in the previous question to solve this.
  intro x h_gt
  rw [abs_of_nonneg h_gt]
  exact Eq.symm (two_mul x)


lemma yadayada_by_cases : A ∨ ¬A := by
  by_cases A
  case pos h => left; exact h
  case neg h => right; exact h


lemma proving_if : if 0 < x then |x| = x else |x| = -x := by
  split
  case isTrue h =>
    -- Find with `exact?`
    exact abs_of_pos h
  case isFalse h =>
    -- Find with `rw?`
    rw [@abs_eq_neg_self]
    -- Find with `exact?`
    exact le_of_not_gt h


lemma proof_by_induction (n : ℕ) : ∃ k, 2 * k + 1 = n ∨ 2 * k = n := by
  induction n
  case zero =>
    use 0
    right
    rfl
  case succ m ih =>
    -- m = n + 1
    obtain ⟨k, ih⟩ := ih
    cases ih
    case inl h =>
      use k + 1
      right
      -- Omega solves Natural number things really well
      omega
    case inr h =>
      use k
      left
      omega


def f (x : ℝ) := x + 5


lemma using_unfold : f (10 + x) = 10 + f (x) := by
  unfold f
  linarith


lemma infi : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ (f x - f (x + δ)) < ε := by
  intro ε h_epsilon
  use ε
  constructor
  case left => exact h_epsilon
  case right =>
    unfold f
    linarith


lemma lets_learn_about_simp (h : x = 10)
: 0 <= 1 + x / 2 * 2 - 1 := by
  simp
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
    have : |a| = a := by exact abs_of_nonneg ha
    have : |a / 2| = a / 2 := by exact abs_of_nonneg ha'
    linarith
  case neg ha =>
    push_neg at ha
    have ha' : a/2 < 0 := by linarith
    simp [abs_of_neg ha, abs_of_neg ha']
    linarith


def array_max (array : Array ℝ) (start : ℕ) (h : array.size > 0) :=
  if _ : start >= array.size then
    array[array.size - 1]
  else
    max array[start] (array_max array (start + 1) h)
