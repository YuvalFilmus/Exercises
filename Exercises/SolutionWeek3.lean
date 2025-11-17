/-
Proving theorems in Lean: Lean and Mathlib for bigger projects.
Yuval Filmus, Shachar Itzhaky, ∧ Jonathan Reicher, 2025
-/

import Mathlib.Tactic


/-
In this file, we will learn using programming concepts such as types and namespaces,
to help us in defining mathematics, and to make proofs easy to construct.

You will learn about: `namespace`, `inductive`, `structure`, `Type`, `Prop`
`Subtype`, `class`, `Finset`, .
-/


-- First exercise:
-- Let's prove that barbers do not exist.
-- The Barber Paradox is a just a logical statement which one might find
-- suprising.


structure Person where
  name : String


structure Town where
  people : Finset Person
  shaves : (p₁ : Person) → (p₂ : Person) → p₁ ∈ people → p₂ ∈ people → Prop


/--
This abbreviation let's us use `Resident t` as a shorthand for `{ p // p ∈ t.people }`.
`{ p // p ∈ t.people }` is a `Subtype Person`. It is a new type, containing all `Person` that
are members of the town.
-/
abbrev Resident (t : Town) : Type := { p // p ∈ t.people }


/--
This abbreviation is under the `Resident` namespace. That means that you can use `a.shaves b`
as a short for `t.shaves a b` when `a : Resident t`.
-/
abbrev Resident.shaves {t : Town} (a b : Resident t) :=
  t.shaves a b a.property b.property
/-
Could have also written it as:
namespace Resident

abbrev shaves {t : Town} (a b : Resident t) :=
  t.shaves a b a.property b.property

end Resident
-/


/-- And this is a function to construct a `Resident t` -/
def Resident.mk (t : Town) (p : Person) (h : p ∈ t.people) : Resident t := ⟨p, h⟩


-- This structure is different: the `: Prop` below makes this type a proposition. In practice,
-- propositions and regular types are almost the same. We will see the difference later.
structure IsBarber {t : Town} (b : Resident t) : Prop where
  proof : ∀ p, b.shaves p ↔ ¬ p.shaves p


theorem paradox : ¬ ∃ t, ∃ b : Resident t, IsBarber b := by
  by_contra! h
  obtain ⟨t, b, h⟩ := h
  obtain hB := h.proof b
  by_cases b.shaves b
  case pos hShaves =>
    have hNotShaves := hB.mp hShaves
    contradiction
  case neg hNotShaves =>
    have hShaves := hB.mpr hNotShaves
    contradiction


-- It seems like barbers were a lie all along!
-- Of course, that's just because of our flawed definition


structure IsBarber' {t : Town} (b : Resident t) where
  proof : ∀ p, p ≠ b → (b.shaves p ↔ ¬ p.shaves p)


theorem solution : ∃ t, ∃ b : Resident t, IsBarber' b := by
  -- Use `use` to specify `b`.
  let b : Person := { name := "Oleg" }
  let t : Town := {
    people := { b }
    shaves _ _ _ _ := False
  }
  use t
  let b' := Resident.mk t b (by exact Finset.mem_singleton.mpr rfl)
  use b'
  -- Here we need to show that `b` is a barber.
  constructor
  -- `constructor` turns the goal into creating the proof in the definition of
  -- `IsBarber`.
  intro p h_p_neq_b
  suffices p = b' by contradiction
  have : p.val ∈ t.people := by exact p.property
  -- Found with "loogle"
  apply Finset.mem_singleton.mp
  -- Found with `exact?`
  exact Finset.insert_eq_self.mp rfl


-- Good job!
-- Now let's learn about inductive types.


-- We are actually going to use a namespace, because we are defining names that
-- already exist in Mathlib. Defining a namespace let's you avoid this naming
-- conflict.
namespace SomeInductiveTypes


inductive Tree (α : Type)
  | leaf : Tree α
  | branch (val : α) (left : Tree α) (right : Tree α) : Tree α


variable {α : Type}


def Tree.sum (t : Tree Nat) :=
  match t with
  | .leaf => 0
  | .branch val left right => val + left.sum + right.sum


def Tree.toList (t : Tree Nat) :=
  match t with
  | .leaf => []
  | .branch val right left => [val] ++ left.toList ++ right.toList


lemma sum_eq_toList_sum (t : Tree Nat) : t.sum = t.toList.sum := by
  induction t
  case leaf =>
    unfold Tree.sum Tree.toList
    -- Found with `exact?`. Could have also used `simp`
    exact rfl
  case branch val left right ih₁ ih₂ =>
    unfold Tree.sum Tree.toList
    simp
    omega


abbrev Var := String
abbrev Vars := Finset String
abbrev Assignment (vars : Vars) := (v : Var) → v ∈ vars → Bool


def Assignment.convert {v₁ v₂} (h : v₂ ⊆ v₁ := by simp) (a : Assignment v₁) : Assignment v₂ :=
  fun v h_v_mem_v₂ => a v (by
    apply Finset.mem_of_subset h
    exact h_v_mem_v₂
  )


inductive Formula : Vars → Type
  | var (v : Var) : Formula { v }
  | and {v₁ v₂} (left : Formula v₁) (right : Formula v₂) : Formula (v₁ ∪ v₂)
  | or {v₁ v₂} (left : Formula v₁) (right : Formula v₂) : Formula (v₁ ∪ v₂)
  | not {v₁} : Formula v₁ → Formula v₁
  | extend {v₁ v₂} : Formula v₁ → Formula (v₁ ∪ v₂)


def Formula.eval {vars} (f : Formula vars) (a : Assignment vars) : Bool :=
  -- Define this function, so the lemmas below are true. Then prove them.
  match f with
  | var v => a v (by exact Finset.mem_singleton.mpr rfl /- `exact?` -/)
  | or left right =>
    left.eval a.convert ∨ right.eval a.convert
  | and left right =>
    left.eval a.convert ∧ right.eval a.convert
  | not inner => ¬ inner.eval a
  | extend inner => inner.eval a.convert


lemma var_or_not_var_eval_eq_true {v a}
  : ((Formula.var v).or (Formula.var v).not).eval a = true := by
    -- Giving `simp` the definition of `eval`, it manages to simplify it
    -- completely.
    simp [Formula.eval]


lemma or_not_eval_eq_true {vars} {f : Formula vars} {a}
  : (f.or f.not).eval a = true := by
    -- Giving `simp` the definition of `eval`, it manages to simplify it
    -- completely.
    -- `simp [Formula.eval, Assignment.convert]`
    -- But here is more brutal solution:
    unfold Formula.eval
    simp
    by_cases f.eval a.convert
    case pos h =>
      left
      assumption
    case neg h_not =>
      replace h_not : f.eval a.convert = false := by
        -- `exact?`
        exact eq_false_of_ne_true h_not
      right
      unfold Formula.eval
      simp
      assumption


lemma and_iff {x y h_x h_y a}
: ((Formula.var x).and (Formula.var y)).eval a ↔ (a x h_x ∧ a y h_y) := by
  -- Here again, the proof can be super simple...
  simp [Formula.eval, Assignment.convert]


class Tauto {vars} (f : Formula vars) : Prop where
  isTrue : ∀ a, f.eval a = true


instance {vars} {f : Formula vars} : Tauto (f.or f.not) where
  isTrue := by
    intro a
    exact or_not_eval_eq_true


instance {v₁ v₂} {f₁ : Formula v₁} {f₂ : Formula v₂} [Tauto f₁]
: Tauto (f₁.or f₂) where
  isTrue := by
    intro a
    unfold Formula.eval
    simp
    rw [Tauto.isTrue]
    left
    rfl


-- The magic of type classes is that they can be generated by Lean when
-- needed!
example {v vars} {f₁ : Formula vars} {f₂ : Formula vars} {a}
: ((((Formula.var v).or (Formula.var v).not).or f₁).or f₂).eval a = true := by
  -- Lean automatically figures out that the formula above is `Tauto`
  apply Tauto.isTrue


-- Lean uses these type classes for operator overloading.

-- +
instance {v₁ v₂} : HAdd (Formula v₁) (Formula v₂) (Formula (v₁ ∪ v₂)) where
  hAdd a b := a.or b
-- *
instance {v₁ v₂} : HMul (Formula v₁) (Formula v₂) (Formula (v₁ ∪ v₂)) where
  hMul a b := a.and b
-- unary -
instance {vars} : Neg (Formula vars) where
  neg := Formula.not

-- Using `"x".var` instead of `Formula.var "x"`
abbrev _root_.String.var := Formula.var

-- Now we can use some arguably nicer syntax!
def myFormula := "x".var + -"y".var
#eval myFormula
