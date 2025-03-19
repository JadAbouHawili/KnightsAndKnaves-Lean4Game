import Game.Metadata
import Game.LevelLemmas.dsl_KnightsAndKnaves

World "DSL_Knights_Knaves"
Level 6

Title ""

Introduction
"
You have met a group of 2 islanders. Their names are Robert and Ira.

Robert says: Ira is my type.
Ira says: Robert is truthful.

Let's first prove `Robert.isKnight`
"

open Islander
Statement {Ira Robert : Islander}
{stR : Robert said (Ira.isKnight ↔ Robert.isKnight) }
{stI : Ira said Robert.isKnight}
: Robert.isKnight ∧ Ira.isKnight := by 
  have RKnight : Robert.isKnight
  Hint 
  "
We will do this by assuming `Robert.isKnave` then proving `False` i.e by proving `¬Robert.isKnave`. Change the goal from knight to knave.
  "
  knight_to_knave
  Hint 
  "
Assume `Robert.isKnave`
  "
  intro RKnave
  Hint 
  "
Now that `Robert.isKnave` , `Ira` was lying becase `¬Robert.isKnight`.
  "
  knave_to_knight at RKnave
  have IKnave := said_knave stI RKnave
  Hint 
  "
But now, `Robert` and `Ira` have the same type. So we can conclude `Robert` is a knight giving us the contradiction we want.
  "
  knight_to_knave at RKnave
  knight_to_knave at stR
  rw [not_iff_not] at stR
  have : Ira.isKnave ↔ Robert.isKnave := by 
    exact iff_of_true IKnave RKnave
    --exact (iff_true_right RKnave).mpr IKnave
  have RKnight := said_knight stR this 
  contradiction

  Hint
  "
Now that `Robert.isKnight` , `Ira` is telling the truth so is a knight as well.

We have the goal.
  "
  have IKnight := said_knight stI RKnight
  constructor
  assumption ; assumption

Conclusion
"
"
