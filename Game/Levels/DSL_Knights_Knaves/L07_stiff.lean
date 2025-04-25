import Game.Metadata
import Game.LevelLemmas.dsl_KnightsAndKnaves

World "DSL_Knights_Knaves"
Level 7

Title ""

Introduction
"
You have met a group of 2 islanders. Their names are Robert and Ira.

`Robert` says: `Ira` is my type.

`Ira` says: `Robert` is truthful.

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
Change the goal from `knight_to_knave`.
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
Conclude that `Ira` is a knave using `¬Robert.isKnight`.

After concluding `Ira.isKnave`:

But now, `Robert` and `Ira` have the same type.
Change the goal to `Robert.isKnight ↔ Ira.isKnight` and conclude from this that `Robert.isKnight`.


To prove the iff statement, here are some relevant theorems:
- iff_of_true
- iff_of_false 
- not_iff_not , not_iff_not.symm
and converting from `knight_to_knave` or vice versa.

You could even use `constructor` and prove every implication.
  "
  knave_to_knight at RKnave
  have IKnave := said_knave stI RKnave
  knight_to_knave at RKnave
  knight_to_knave at stR
  rw [not_iff_not] at stR
  have : Ira.isKnave ↔ Robert.isKnave := by 
    exact iff_of_true IKnave RKnave
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
NewTheorem not_iff_not
