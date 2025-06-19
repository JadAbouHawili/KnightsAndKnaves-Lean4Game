import Game.Metadata
import Game.LevelLemmas.dsl_KnightsAndKnaves
open Islander

World "DSL_Knights_Knaves" 
Level 5

Title "" 

Introduction 
"
`A` says 'I am a knave or `B` is a knight'.
"

-- prob 29
Statement
{A B : Islander}
{stA : A said (A.isKnave ∨ B.isKnight)}
: A.isKnight ∧ B.isKnight := by 
  Hint (strict := true)
  "
Change the goal to `A.isKnight`
  "
  have AKnight : A.isKnight
  Hint (strict := true)
  "
Transform the goal from `knight_to_knave`.
  "
  knight_to_knave
  intro AKnave
  Hint
  "
Conclude that `A`'s statement is false.
  "
  have cont := knave_said stA AKnave 
  Hint
  "
Simplify `{cont}` using `not_or`
  "
  rw [not_or] at cont
  Hint
  "
The left side of `{cont}` is `¬isKnave A` (`{cont}.left : ¬isKnave A`) which contradicts `{AKnave} : isKnave A`.
  "
  have := cont.left
  contradiction

  Hint
  "
Conclude `A`'s statement.
  "
  have st := knight_said stA AKnight
  Hint
  "
The left side of or is false and so can be simplified.
  "
  knave_to_knight at st
  simp [AKnight] at st
  Hint
  "
Close the goal
  "
  constructor
  assumption
  assumption

