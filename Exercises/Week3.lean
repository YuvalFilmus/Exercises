import Mathlib.Tactic


-- NOTE: WIP.


-- Let's prove that barbers do not exist.
-- The Barber Paradox is a just a logical statement which one might find
-- suprising.


structure Person where
  name : String


structure IsBarber (b : Person) where
  shaves : Person → Person → Prop -- A relation over two elements
  proof : ∀ p : Person, shaves b p ↔ ¬ shaves p p


theorem paradox (b : Person) : IsBarber b → False := by
  sorry


-- It seems like barbers were a lie all along!
-- Of course, that's just because of our flawed definition


structure IsBarber' (b : Person) where
  shaves : Person → Person → Prop -- A relation over two elements
  proof : ∀ p : Person, p ≠ b → (shaves b p ↔ ¬ shaves p p)


theorem solution : ∃ b, Nonempty (IsBarber' b) := by
  sorry
