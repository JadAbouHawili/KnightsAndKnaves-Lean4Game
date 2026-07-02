
import Game.MathlibTheorems
import Game.LevelLemmas.Logical

World "Logic"
Level 3

Title "And, `∧`"
Introduction
"


Logical connectives are either defined by their introduction and elimination rules or by truth
tables.

An introduction rule 'introduces' a symbol , in this case proving a statement of `and`.

An elimination rule 'eliminates' a symbol extracting information from it. For an expression `P and Q`
, applying the elimination rule would give you a proof of `P` and a proof of `Q` separately which
will be explored in the next level.

"

Statement (P Q : Prop) (hP : P and Q)
  : P  := by
  {
    Hint(hidden:=true)
    "

    "
    exact hP.left
  }

Conclusion
"
"

NewTheorem And.intro
NewDefinition logic_and
NewTactic constructor
