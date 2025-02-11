import Game.Metadata


World "DSL_Knights_Knaves" 
Level 2

Title "" 

Introduction 
"
"

open Islander
Statement {A B C : Islander} 
{hB : B said (A said A.isKnave)}
{hC : C said B.isKnave}
: B.isKnave and C.isKnight := by 
  have BKnave : B.isKnave
  -- need to introduce apply in this game
  apply notisKnight_isKnave
  intro BKnight
  have hA := knight_said hB BKnight
  exact dsl_iamknave hA

  constructor
  assumption

  have CKnight := said_knight hC BKnave
  assumption

Conclusion 
"
"
NewTheorem dsl_iamknave
