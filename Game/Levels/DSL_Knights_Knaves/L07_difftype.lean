import Game.Metadata
import Game.LevelLemmas.dsl_KnightsAndKnaves

World "DSL_Knights_Knaves" 
Level 7

Title ""

Introduction 
"
"

open Islander
example
{A B : Islander}
(stA : A said B.isKnight)
(stB : B said ( ¬ (A.isKnight ↔ B.isKnight) ) ) 
: A.isKnave and B.isKnave := by 
  have AKnave : A.isKnave
  knave_to_knight 
  intro AKnight 
  have BKnight := knight_said stA AKnight
  have notsame := knight_said stB BKnight
  exact notsame (iff_of_true AKnight BKnight)

  have BKnave := knave_said stA AKnave
  knight_to_knave at BKnave 
  constructor
  repeat assumption

Conclusion
"
"
