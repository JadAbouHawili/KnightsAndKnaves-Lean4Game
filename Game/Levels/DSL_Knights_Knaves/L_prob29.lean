import Game.Metadata
import Game.LevelLemmas.dsl_KnightsAndKnaves
open Islander

-- prob 29
example
{A B : Islander}
{stA : A said (A.isKnave ∨ B.isKnight)}
: A.isKnight ∧ B.isKnight := by 
  have AKnight : A.isKnight 
  knight_to_knave 
  intro AKnave
  have cont := knave_said stA AKnave 
  push_neg at cont
  have := cont.left
  contradiction

  knave_to_knight at stA
  simp [AKnight] at stA
  have BKnight := knight_said stA AKnight 
  constructor
  repeat assumption

