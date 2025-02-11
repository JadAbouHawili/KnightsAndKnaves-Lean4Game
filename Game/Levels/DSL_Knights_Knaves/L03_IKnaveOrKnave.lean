import Game.Metadata
#check dsl_iamknave
World "DSL_Knights_Knaves" 
Level 3

Title "" 

Introduction 
"
"

--`A` says 'I am a knave or `B` is a knave'.
open Islander
Statement 
{A B : Islander}
{stA : A said (A.isKnave or B.isKnave)}
: A.isKnight and B.isKnave := by 
  have AKnight : A.isKnight 
  apply notisKnave_isKnight
  intro AKnave

  apply said_knight at stA
  have orexp: isKnave A or isKnave B
  left 
  assumption
  have AKnight := stA orexp
  contradiction
   
  constructor
  assumption 
  have orexp := knight_said stA AKnight
  apply notleft_right at orexp 
  --exact orexp (isKnight_notisKnave AKnight)
  apply orexp
  intro 
  contradiction

  --simp [AKnight,isKnight_notisKnave] at orexp
  --assumption

Conclusion 
"
"
