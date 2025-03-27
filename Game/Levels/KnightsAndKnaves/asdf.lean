import Game.Metadata_KnightsAndKnaves

World "KnightsAndKnaves"
Level 5

Title ""

Introduction
"
"

open settheory_approach
#check dis
#check Inhabitant

variable [DecidableEq Inhabitant]
#check inleft_notinright dis
#check inleft_notinrightIff
#check either
Statement
{A : Inhabitant}
{B : Inhabitant}
{either : A ∈ Knight ∨ A ∈ Knave}
(hA : A ∈ Knight )
(hA' : A ∈ Knave )
(hB : B ∈ Knight)
(hB' : B ∈ Knave)
: 1=2 := by
  -- i can have this take A instead of either as argument then use an axiom that gives the or, this tactic wouldn't work for all instantces of knight
  #check either
  set_knight_to_knave B at *
  set_knave_to_knight B at *
  have : False := disjoint_without hA hA'
  have : A ∈ Knight := by 
    have : B ∈ Knave := by 
      set_knave_to_knight B
      sorry
    set_knave_to_knight B at this
    set_knight_to_knave A
    sorry
  contradiction

Conclusion
"
"
--NewTheorem settheory_approach.disjoint_without
