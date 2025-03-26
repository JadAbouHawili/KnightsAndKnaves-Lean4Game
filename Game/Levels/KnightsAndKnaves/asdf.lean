import Game.Metadata_KnightsAndKnaves

World "KnightsAndKnaves"
Level 5

Title ""

Introduction
"
"

--Statement
--  :  := by
--
--  {
--
--  }

open settheory_approach
#check dis
#check Inhabitant
variable [DecidableEq Inhabitant]
Statement 
{A : Inhabitant}
(hA : A ∈ Knight )
(hA' : A ∈ Knave )
: 1=2 := by 
  have : False := disjoint_without hA hA'
  contradiction

Conclusion 
"
"
--NewTheorem settheory_approach.disjoint_without
