import Game.Metadata

World "DSL_Knights_Knaves" 
Level 4

Title "" 

Introduction 
"
"

open Islander
set_option push_neg.use_distrib true
Statement 
{A B : Islander}
{stA : A said (A.isKnave  and  ¬B.isKnave) }
: ¬A.isKnight and B.isKnave := by 
  have AnK : ¬A.isKnight  
  intro AKnight
  have AKnave := knight_said stA AKnight
  have AKnave := AKnave.left
  contradiction

  constructor
  assumption
  have st := notknight_said stA AnK 
  --simp at st 
  --#check not_and
  push_neg at st
  have AKnave := notisKnight_isKnave AnK
  simp [AKnave] at st
  --have := notleft_right st AKnave
  assumption

Conclusion 
"
"
