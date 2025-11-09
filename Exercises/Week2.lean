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


lemma branching_by_cases : (¬A → B) → A ∨ B := by
  intro h₁
  by_cases A
  case pos h₂ => left; exact h₂
  case neg h₃ => right; exact h₁ h₃


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
  by_contra! h
  obtain ⟨x₁, hx₁⟩ := h₁
  obtain ⟨x₂, hx₂⟩ := h₂
  have h₁ : f x = true := by
    rw [←hx₁]
    symm
    apply h_certificate
    intro n hn
    have := h n
    contradiction
  have h₂ : f x = false := by
    rw [←hx₂]
    symm
    apply h_certificate
    intro n hn
    have := h n
    contradiction
  rw [h₁] at h₂
  contradiction


/-- A function is periodic (like sin or cos) -/
def has_period (f : ℕ → ℕ) (r : ℕ) :=
  ∀ n, f (n + r) = f n


lemma periodicity {f r} (hf : has_period f r) : ∀ m, has_period f (m*r) := by
  intro m
  induction m
  case zero =>
    intro n
    simp
  case succ m ih =>
    intro n
    unfold has_period at *
    suffices f ((n + m * r) + r) = f n by
      have h : n + (m + 1) * r = (n + m * r) + r := by linarith
      rw [h]
      exact this
    rw [hf]
    rw [ih]


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
  suffices array_max a upTo h₂ ∈ a by
    intro x h_x_in_a
    apply h₁
    case a => exact h_x_in_a
    case a => exact this
  induction upTo
  case zero =>
    unfold array_max
    split -- `0 >= a.size`?
    case isTrue h =>
      have : ¬ 0 >= a.size := by omega
      contradiction
    case isFalse h => 
      simp
      -- `exact?` also finds a solution
  case succ upTo' ih =>
    unfold array_max
    simp
    split
    case isTrue h =>
      -- `exact?`
      exact Array.getElem_mem (array_max._proof_4 a (upTo' + 1) h₂)
    case isFalse h₃ =>
      set x := a[upTo' + 1]
      set y := array_max a upTo' h₂
      have : x ∈ a := by
        -- Found by `exact?`
        exact Array.getElem_mem (Decidable.byContradiction fun a_1 ↦ array_max_of_all_equal._proof_1_2 a upTo' h₃ a_1)
      by_cases x < y
      case pos h₄ =>
        have : max x y = y := by
          -- `exact?`
          exact max_eq_right_of_lt h₄
        rw [this]
        assumption
      case neg h₄ =>
        have : max x y = x := by
          have : y <= x := by linarith
          -- `exact?`
          exact max_eq_left this
        rw [this]
        assumption

