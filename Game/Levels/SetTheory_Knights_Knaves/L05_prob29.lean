import Game.LevelLemmas.settheory_KnightsAndKnaves


open Inhabitant

World "SetTheory_Knights_Knaves"
Level 5

Title "Intro"

Introduction
"
`A` says 'I am a knave or `B` is a knave'.
"


Statement
{stA : A ∈ Knight ↔ (A ∈ Knave ∨ B ∈ Knight)}
{stAn : A ∈ Knave ↔ ¬(A ∈ Knave ∨ B ∈ Knight)}
: A ∈ Knight ∧ B ∈ Knight := by
  Hint (strict := true)
  "
Change the goal to `A ∈ Knight`
  "
  have AKnight : A ∈ Knight
  Hint (strict := true)
  "
Transform the goal from `knave_interp`.
  "
  knave_interp
  intro AKnave
  Hint
  "
Conclude that `A`'s statement is false.
  "
  have cont := stAn.mp AKnave
  Hint
  "
Simplify `{cont}` using `not_or`
  "
  rw [not_or] at cont
  Hint
  "
The left side of `{cont}` is `¬isKnave A` (`{cont}.left : A ∉ Knave`) which contradicts `{AKnave}
: A ∈ Knave`.
  "
  have := cont.left
  contradiction

  Hint
  "
Conclude `A`'s statement.
  "
  have st := stA.mp AKnight
  Hint
  "
The left side of or is false and so can be simplified.
  "
  knight_interp at st
  simp [AKnight] at st
  Hint
  "
Close the goal
  "
  constructor
  assumption
  assumption

