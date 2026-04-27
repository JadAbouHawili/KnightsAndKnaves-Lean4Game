import Game.LevelLemmas.settheory_KnightsAndKnaves

open Inhabitant

World "SetTheory_Knights_Knaves"
Level 8

Title "Intro"

Introduction
"
You have met a group of 2 islanders. Their names are `Robert` and `Ira`.

`Robert` says: `Ira` is my type.

`Ira` says: `Robert` is truthful.

A knight or a knave will say they are the same type as a knight. So when `Robert` says they are the same type as `Ira`, we know that `Ira` is a knight.

Let's start by proving `Ira.isKnight`
"

theorem iff_assoc {P Q R: Prop}
: ((P ↔ Q) ↔ R) ↔ (P ↔ (Q ↔ R)) := by{
  grind
  }

-- changes made from the original copies form DSL , change corresponding level in DSL if necessary...
Statement
{Robert Ira : Inhabitant}
{stR : Robert ∈ Knight ↔ (Robert ∈ Knight ↔ Ira ∈ Knight)}
{stI : Ira ∈ Knight ↔ (Robert ∈ Knight)}
:  Robert ∈ Knight and Ira ∈ Knight := by {
-- stR looks ugly
  Hint
  "
  "
  rw [iff_assoc.symm] at stR
  rw [iff_self] at stR
  rw [true_iff] at stR
  have hR := stI.mp stR
  constructor
  assumption ; assumption
}

/-
example
{Robert Ira : Inhabitant}
{stR : Robert ∈ Knight ↔ (Robert ∈ Knight ↔ Ira ∈ Knight)}
{stI : Ira ∈ Knight ↔ (Robert ∈ Knight)}
:  Robert ∈ Knight and Ira ∈ Knight := by {
  have IKnight : Ira ∈ Knight
  Hint
  "
Assume by contradiction that `¬Ira.isKnight` using the `by_contra` tactic.
  "
  by_contra nIKnight
  Hint
  "
  We will now simplify `stR`.

  Because `¬Ira.isKnight`, `Robert.isKnight ↔ Ira.isKnight ` can be simplified to `¬ Robert.isKnight`
  "
  simp only[nIKnight] at stR
  Hint
  "
  `stR` now becomes `Robert said ¬ Robert.isKnight`.

  Change that to `Robert said Robert.isKnave`

  "
  have hR := stI.mp IKnight
  constructor
  assumption ; assumption
  /-
  set_knight_to_knave at stR
  Hint
  "
`Robert` is saying 'I am a knave' which is a contradiction. Use the appropriate theorem
  "
  Hint (hidden := true)
  "
`dsl_iamknave`
  "
  exact IamKnave stR

  Hint
  "
Now that `Ira` is a knight, conclude that `Robert` is a knight and close the goal.
  "
  have RKnight := knight_said stI IKnight
  constructor
  assumption ; assumption
  -/

  }
-/

Conclusion
"
"
