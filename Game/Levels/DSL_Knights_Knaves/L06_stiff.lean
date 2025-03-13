import Game.Metadata
import Game.LevelLemmas.dsl_KnightsAndKnaves

World "DSL_Knights_Knaves"
Level 7

Title ""

Introduction
"
You have met a group of 2 islanders. Their names are Robert and Ira.

    Robert says: Ira is my type.
    Ira says: Robert is truthful.
"

open Islander
Statement {Ira Robert : Islander}
{stR : Robert said (Ira.isKnight ↔ Robert.isKnight) }
{stI : Ira said Robert.isKnight}
: Robert.isKnight ∧ Ira.isKnight := by 
  have RKnight : Robert.isKnight
  knight_to_knave
  intro RKnave
  knave_to_knight at RKnave
  have IKnave := said_knave stI RKnave
  knight_to_knave at RKnave
  knight_to_knave at stR
  rw [not_iff_not] at stR
  have : Ira.isKnave ↔ Robert.isKnave := by 
    exact (iff_true_right RKnave).mpr IKnave
  have RKnight := said_knight stR this 
  contradiction

  have IKnight := said_knight stI RKnight
  constructor
  assumption ; assumption

Conclusion
"
"
