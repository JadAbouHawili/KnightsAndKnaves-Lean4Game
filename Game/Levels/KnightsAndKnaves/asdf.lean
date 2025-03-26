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
axiom eith (A : Inhabitant): A ∈ Knight or A ∈ Knave 
macro "set_knight_to_knave_notiff" t2:term "at"  t1:Lean.Parser.Tactic.locationWildcard : tactic =>
do`(tactic| simp [inleft_notinrightIff (eith $t2) dis] at $t1)

variable [DecidableEq Inhabitant]
#check inleft_notinright dis
#check inleft_notinrightIff
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
  #check eith
  set_knight_to_knave_notiff B at *
  have : False := disjoint_without hA hA'
  contradiction

Conclusion
"
"
--NewTheorem settheory_approach.disjoint_without
