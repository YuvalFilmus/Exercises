/-
Proving theorems in Lean: a quick introduction
Yuval Filmus, Shachar Itzhaky, ∧ Jonathan Reicher, 2025
-/

import Mathlib.Tactic


/-
In this file you will learn how to use Lean, logical connectives, and quantifiers.
This file introduces you to the following symbols: →, ↔, ∧, ∨, ¬, ∀, and ∃
And to the following tactics: `intro`, `exact`, `apply`, `assumption`, `cases`,
`constructor`, `left`, `right` and `contrapose!`.

Everything you need is in the slides, but don't hesitate to ask a question.
https://www.icloud.com/keynote/0f9WShIZaWKcNfbl2QU1-k2JA#Lean2025
Solutions can be found in `SolutionWeek1.lean`.
-/

-- Ignore me, I just define globals
variable {A B C : Prop}


lemma implication_1 : A → (B → A) := by
  intro h_A
  intro _
  exact h_A

lemma implication_2 : A → (A → B) → B := by
  intro h_A h_A_to_B -- Same as `intro h_A` then `intro h_A_to_B`
  exact h_A_to_B h_A

lemma implication_3 : (A → (B → C)) → ((A → B) → (A → C)) := by
  intro h₁ h₂ h_a
  apply h₁ h_a
  apply h₂
  exact h_a

lemma proving_iff : A ↔ A := by
  constructor
  case mp =>  -- Remember Modus Ponens from Logic?
    intro h
    exact h
  case mpr => -- Modus Ponens - reversed!
    intro h
    exact h

lemma using_iff : (A ↔ B) → B → A := by
  intro h_iff
  intro h_B
  exact h_iff.mpr h_B

lemma proving_or : A → A ∨ B := by
  intro h_A
  left
  assumption -- Same as `exact h_A` (Finds `h_A` automatically)

lemma using_or : A ∨ B → B ∨ A := by
  intro h_or
  cases h_or
  case inl h =>
    right
    assumption
  case inr h =>
    left
    assumption

lemma proving_and : A → (A → B) → A ∧ B := by
  intro h_A h_A_to_B
  constructor
  case left => assumption
  case right =>
    apply h_A_to_B
    exact h_A

lemma using_and : A ∧ B → A ∨ B := by
  intro h_and
  right
  exact h_and.right

-- Let's see if you can use everything you learned so far!
lemma complex : A ∨ (A ∧ B) ↔ A := by
  constructor
  case mp =>
    intro h_or
    cases h_or
    case inl h => exact h
    case inr h_and => exact h_and.left
  case mpr =>
    intro h
    left
    exact h

lemma using_negation_1 : A → ¬ A → False := by
  -- Negation is just implication: ¬ A is just (A → False)
  intro h_A h_not_A
  exact h_not_A h_A -- Could have also used `contradiction`

lemma proving_negation_1 : ¬ A → ¬ (A ∧ B) := by
  intro h_not
  intro h_A_and_B -- ¬ (A ∧ B) is the same as (A ∧ B → False)
  exact h_not h_A_and_B.left
  -- Another possible solution:
  -- contrapose!
  -- intro h_A_and_B
  -- exact h_A_and_B.left

lemma proving_negation_2 : (A → B) → (¬ B → ¬ A) := by
  intro h_A_to_B h_not_B
  intro h_A
  apply h_not_B
  exact h_A_to_B h_A

lemma proving_negation_with_contrapose : (¬ A → ¬ B) → (B → A) := by
  -- This one is hard to prove without using `contrapose!`
  intro h_not_A_to_not_B
  contrapose! -- Turn `B → A` to `¬A → ¬B`
  assumption
  -- Another possible solution:
  -- intro h hB
  -- contrapose! h
  -- constructor <;> assumption


/-
Good job getting up to this point!
-/


variable {P : ℕ → ℕ → Prop}
variable {Q : ℕ → Prop}


lemma using_forall : (∀ n, P 0 n) → P 0 0 := by
  intro h_forall
  exact h_forall 0 -- For-alls can be used just like implications

lemma proving_forall : (∀ n m, P n m) → (∀ n, P n n) := by
  intro h_forall
  intro n
  apply h_forall -- But apply knows how to choose the variables automatically

lemma proving_exists : (∀ n, Q n) → ∃ n, Q n := by
  intro h
  use 0
  apply h

lemma using_exists : ¬ (∃ n, Q n ∧ ¬ Q n) := by
  intro ⟨n, ⟨h_yes, h_no⟩⟩
  contradiction

lemma swap_quantifiers : (∃ x, ∀ y, P x y) → ∀ y, ∃ x, P x y := by
  intro h
  obtain ⟨x, h⟩ := h
  intro y
  use x
  apply h

lemma dependent_arrow : (A → B) → (h: A) → B := by
  -- All implications are actually dependent.
  -- `X → Y` is the same as `(_ : X) → Y`
  intro h
  exact h

lemma proving_functions : ∃ f : ℕ → ℕ, ∀ n, f n = 0 := by
  use fun n => 0
  intro n
  rfl

variable {X Y Z : Type}

-- Ignore the fact that we use `def` instead of `lemma`
def using_functions : (f : X → Y) → (g : Y → Z) → (X → Z) := by
  intro f g
  exact fun x => (g (f x))

/-
Good job - you finished all the material!
Now, for extra practice, here are some harder questions.
They are completely optional, and they will test your skill.
You may do them in whatever order you feel like.
-/

lemma inverse_of_invertible {f : ℕ → ℕ}
  (inj : ∀ x₁ x₂, f x₁ = f x₂ → x₁ = x₂)
  (surj : ∀ y, ∃ x, f x = y) :
  ∃ g : ℕ → ℕ, (∀ x, f (g x) = x) ∧ (∀ x, g (f x) = x) := by
  choose g hg using surj
  use g
  constructor
  case left =>
    exact hg
  case right =>
    intro x
    apply inj
    apply hg

lemma XOR_equiv :
  ((A ∧ ¬ B) ∨ (B ∧ ¬ A)) ↔ ((A ∨ B) ∧ (¬ A ∨ ¬ B)) := by
  constructor
  case mp =>
    intro h
    cases h
    case inl h =>
      constructor
      · left; exact h.left
      · right; exact h.right
    case inr h =>
      constructor
      · right; exact h.left
      · left; exact h.right
  case mpr =>
    intro h
    cases h.left
    case inl hA =>
      cases h.right
      case inl hA' => contradiction
      case inr hB' => left; constructor <;> assumption
    case inr hB =>
      cases h.right
      case inl hA' => right; constructor <;> assumption
      case inr hB' => contradiction


lemma MAJ_equiv :
  ((A ∧ B) ∨ (A ∧ C) ∨ (B ∧ C)) ↔ ((A ∨ B) ∧ (A ∨ C) ∧ (B ∨ C)) := by
  constructor
  case mp =>
    intro h
    cases h
    case inl h =>
      constructor
      · left; exact h.left
      constructor
      · left; exact h.left
      · left; exact h.right
    case inr h =>
    cases h
    case inl h =>
      constructor
      · left; exact h.left
      constructor
      · left; exact h.left
      · right; exact h.right
    case inr h =>
      constructor
      · right; exact h.left
      constructor
      · right; exact h.right
      · left; exact h.left
  case mpr =>
    intro h
    obtain ⟨hAB,⟨hAC,hBC⟩⟩ := h
    cases hAB
    case inl hA =>
      cases hBC
      case inl hB =>
        left
        constructor
        · exact hA
        · exact hB
      case inr hC =>
        right; left
        constructor
        · exact hA
        · exact hC
    case inr hB =>
      cases hAC
      case inl hA =>
        left
        constructor
        · exact hA
        · exact hB
      case inr hC =>
        right; right
        constructor
        · exact hB
        · exact hC

lemma aperiodicity_criterion {S : Set ℕ}
  (hrun : ∀ n₀ q, ∃ n ≥ n₀, (∀ i < q, n + i ∈ S) ∧ n + q ∉ S) :
  ¬ ∃ n₀ p, p > 0 ∧ ∀ n ≥ n₀, n ∈ S ↔ n + p ∈ S := by
  by_contra hper -- Same as `intro hper`
  -- proof starts here
  obtain ⟨n₀, p, ⟨hp, hper⟩⟩ := hper
  obtain ⟨n, ⟨hn, hrun⟩⟩ := hrun n₀ p
  have hin : n ∈ S := by
    apply hrun.left 0
    exact hp
  have hout : n + p ∉ S := hrun.right
  have := hper n hn
  have := this.mp hin
  contradiction

