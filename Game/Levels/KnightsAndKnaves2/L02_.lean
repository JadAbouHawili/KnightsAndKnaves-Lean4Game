import Game.Metadata


World "KnightsAndKnaves2" 
Level 2

Title "" 

Introduction 
"
instread of by_contra, rw[not_not] then intro..

Robert says: Ira is my type.
Ira says: Robert is truthful.
"


Statement 
{Robert Ira : Prop}
{stR : Robert ↔ (Ira ↔ Robert)}
{stI : Ira ↔ Robert}
: Robert ∧ Ira := by 
  have : Robert 
  by_contra h
  rw [stR] at h
  contradiction

  have := stI.mpr this
  constructor
  repeat assumption

Conclusion 
"
"
