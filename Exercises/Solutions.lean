/-
Proving theorems in Lean: a quick introduction
Yuval Filmus and Shachar Itzhaky, 2025

Solutions to exercises in Problems.lean.
-/

import Mathlib.Tactic

/-
Proving in Lean:
Working with connectives and quantifiers
-/

section

variable {A B C : Prop}

lemma Axiom1 : A → (B → A) := by
  intro hA _
  exact hA

lemma Axiom2 : (A → (B → C)) → ((A → B) → (A → C)) := by
  intro h₁ h₂ hA
  apply h₁ hA
  apply h₂ hA

lemma Axiom3 : (¬ A → ¬ B) → (B → A) := by
  intro h hB
  contrapose! h
  constructor <;> assumption

lemma XOR_equiv :
  ((A ∧ ¬ B) ∨ (B ∧ ¬ A)) ↔ ((A ∨ B) ∧ (¬ A ∨ ¬ B)) := by
  constructor
  case mp =>
    intro h
    cases h
    case inl h =>
      constructor
      · left; exact h.1
      · right; exact h.2
    case inr h =>
      constructor
      · right; exact h.1
      · left; exact h.2
  case mpr =>
    intro h
    cases h.1
    case inl hA =>
      cases h.2
      case inl hA' => contradiction
      case inr hB' => left; constructor <;> assumption
    case inr hB =>
      cases h.2
      case inl hA' => right; constructor <;> assumption
      case inr hB' => contradiction

end section

lemma nonzero_of_pos {n : ℤ} (hn : n > 0) : n ≠ 0 := by
  contrapose! hn
  subst hn
  rfl

lemma swap_quantifiers {P : ℕ → ℕ → Prop} :
  (∃ x, ∀ y, P x y) → ∀ y, ∃ x, P x y := by
  intro h
  obtain ⟨x, h⟩ := h
  intro y
  use x
  apply h

/-
hint 1: use push_neg to simplify ¬ (...)
hint 2: at the end, try to use omega or aesop
-/
lemma swap_quantifiers_op :
  ∃ P : ℕ → ℕ → Prop,
    ¬ ((∀ y, ∃ x, P x y) → ∃ x, ∀ y, P x y) := by
  use fun x y => x = y
  push_neg
  constructor
  · intro y
    use y
  · intro x
    use x + 1
    omega

lemma aperiodicity_criterion {S : Set ℕ}
  (hrun : ∀ n₀ q, ∃ n ≥ n₀, (∀ i < q, n + i ∈ S) ∧ n + q ∉ S) :
  ¬ ∃ n₀ p, p > 0 ∧ ∀ n ≥ n₀, n ∈ S ↔ n + p ∈ S := by
  by_contra! hper
  -- proof starts here
  obtain ⟨n₀, p, ⟨hp, hper⟩⟩ := hper
  obtain ⟨n, ⟨hn, hrun⟩⟩ := hrun n₀ p
  have hin : n ∈ S := by
    apply hrun.1 0
    exact hp
  have hout : n + p ∉ S := hrun.2
  have := hper n hn
  have := this.mp hin
  contradiction

lemma inverse_of_invertible {f : ℕ → ℕ}
  (inj : ∀ x₁ x₂, f x₁ = f x₂ → x₁ = x₂)
  (surj : ∀ y, ∃ x, f x = y) :
  ∃ g : ℕ → ℕ, (∀ x, f (g x) = x) ∧ (∀ x, g (f x) = x) := by
  choose g hg using surj
  use g
  constructor
  · exact hg
  intro x
  apply inj
  rw [hg]

/-
Proving in Lean:
Common proof strategies
-/

/- Proof by cases -/

-- use abs_eq_self, abs_eq_neg_self, le_of_lt
lemma abs_elem (n : ℤ) : |n| = n ∨ |n| = -n := by
  by_cases n ≥ 0
  case pos h =>
    left
    apply abs_eq_self.mpr
    exact h
  case neg h =>
    right
    apply abs_eq_neg_self.mpr
    push_neg at h
    apply le_of_lt
    exact h

/- Proof by contradiction -/

-- hint: derive contradiction from true = false
lemma cert_nontriv {f : (ℕ → Bool) → Bool}
  (h₀ : ∃ x, f x = true) (h₁ : ∃ x, f x = false)
  {x : ℕ → Bool} {S : Set ℕ}
  (hcert : ∀ y : ℕ → Bool, (∀ n ∈ S, y n = x n) → f y = f x) :
  ∃ n, n ∈ S := by
  by_contra! h
  obtain ⟨x₀, hx₀⟩ := h₀
  obtain ⟨x₁, hx₁⟩ := h₁
  have h₁ : f x = true := by
    rw [←hx₀]; symm
    apply hcert
    intro n hn
    have := h n
    contradiction
  have h₂ : f x = false := by
    rw [←hx₁]; symm
    apply hcert
    intro n hn
    have := h n
    contradiction
  rw [h₁] at h₂
  contradiction

/- Proof by induction -/

def has_period (f : ℕ → ℕ) (r : ℕ) :=
  ∀ n, f (n + r) = f n

/-
 - Following lemmas might be useful:
 - Nat.add_one_mul states (a + 1) * b = a * b + b
 - add_assoc is associativity of addition
-/
lemma periodicity {f r} (hf : has_period f r) :
  ∀ m, has_period f (m*r) := by
  intro m
  induction m
  case zero =>
    intro n
    simp
  case succ m ih =>
    intro n
    rw [Nat.add_one_mul, ←add_assoc, hf, ih]

/- Calculations -/

lemma diameter_of_radius {X : Type _} {d : X → X → ℝ}
  (symm : ∀ x y, d x y = d y x)
  (triangle : ∀ x y z, d x z ≤ d x y + d y z)
  {p : X} {S : Set X} {r : ℝ} (hp : ∀ x ∈ S, d p x ≤ r) :
  ∀ x ∈ S, ∀ y ∈ S, d x y ≤ 2*r := by
  intro x hx y hy
  calc
    d x y ≤ d x p + d p y := by apply triangle
    _ = d p x + d p y := by rw [symm]
    _ ≤ r + r := by gcongr <;> (apply hp ; assumption)
    _ = 2*r := by ring

-- use gcongr and Finset.sum_const
lemma sum_one {n : ℕ} {f : ℕ → ℕ} (hf : ∀ x, f x ≥ 1) :
  ∑ i ∈ Finset.range n, f i ≥ n := by
  calc
    ∑ i ∈ Finset.range n, f i ≥ ∑ i ∈ Finset.range n, 1 := by
      gcongr with i
      apply hf
    _ = (Finset.range n).card * 1 := by
      apply Finset.sum_const
    _ = n := by
      simp

/- Longer proofs -/

open Finset in
lemma exists_finset (S : Finset ℕ) {k : ℕ} (hk : k ≤ #S) :
  ∃ T ⊆ S, #T = k := by
  set n := #S with ←hn
  rw [←hn] at hk
  revert hn
  induction n generalizing S k
  case zero =>
    intro hS
    use ∅
    constructor
    · simp
    · simp; linarith
  case succ n' ih =>
    intro hS
    by_cases k = n' + 1
    case pos hk' =>
      use S
      constructor
      · simp
      · linarith
    case neg hk' =>
      have : S.Nonempty := by
        apply card_pos.mp
        linarith
      obtain ⟨x, hx⟩ := this
      set S' := S.erase x with hS'
      have : ∃ T ⊆ S', #T = k := by
        apply ih
        · rw [hS']
          simp [S.card_erase_of_mem hx]
          omega
        · rw [hS']
          simp [S.card_erase_of_mem hx]
          omega
      obtain ⟨T, hT⟩ := this
      use T
      constructor
      · trans S'
        exact hT.1
        intro i hi
        simp [hS'] at hi
        exact hi.2
      · exact hT.2
