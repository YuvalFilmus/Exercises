import Mathlib.Tactic


-- Let's prove that barbers do not exist.
-- The Barber Paradox is a just a logical statement which one might find
-- suprising.


structure Person where
  name : String


structure IsBarber (b : Person) where
  shaves : Person → Person → Prop -- A relation over two elements
  proof : ∀ p : Person, shaves b p ↔ ¬ shaves p p


theorem paradox (b : Person) : IsBarber b → False := by
  intro h
  obtain hB := h.proof b
  by_cases h.shaves b b
  case pos hShaves =>
    have hNotShaves := hB.mp hShaves
    contradiction
  case neg hNotShaves =>
    have hShaves := hB.mpr hNotShaves
    contradiction


-- It seems like barbers were a lie all along!
-- Of course, that's just because of our flawed definition


structure IsBarber' (b : Person) where
  shaves : Person → Person → Prop -- A relation over two elements
  proof : ∀ p : Person, p ≠ b → (shaves b p ↔ ¬ shaves p p)


theorem solution : ∃ b, Nonempty (IsBarber' b) := by
  -- Use `use` to specify `b`.
  let b : Person := { name := "Oleg" }
  use b
  constructor
  exact {
    shaves p₁ p₂ := (p₁ = b) ∧ (p₂ ≠ b)
    proof := by
      intro p pNeqB
      constructor
      . intro
        intro ⟨hPEqB, hPNeqB⟩
        contradiction
      . intro
        constructor
        . trivial
        . exact pNeqB
  }
