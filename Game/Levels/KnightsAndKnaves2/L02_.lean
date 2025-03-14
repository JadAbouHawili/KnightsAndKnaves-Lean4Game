import Game.Metadata


World "KnightsAndKnaves2" 
Level 2

Title "" 

Introduction 
"
Robert says: Ira is my type.
Ira says: Robert is truthful.

Change the goal to `Robert`
"


Statement 
{Robert Ira : Prop}
{stR : Robert ↔ (Ira ↔ Robert)}
{stI : Ira ↔ Robert}
: Robert ∧ Ira := by 
  have : Robert 
  Hint
  "
Assume `¬Robert` and prove `False`.

`by_contra nRobert` does that.
  "
  by_contra h
  Hint 
  "
`Robert` is equivalent to `Ira ↔ Robert`

So `¬Robert` is equivlent to `¬(Ira ↔ Robert)` contradicting `stI`.
  "
  rw [stR] at h
  contradiction

  Hint 
  "
Now that you know `Robert`, conclude `Ira`
  "
  have := stI.mpr this
  constructor
  repeat assumption

Conclusion 
"
"
