import Game.Metadata


World "KnightsAndKnaves2" 
Level 1

Title "" 

Introduction 
"
A very special island is inhabited only by knights and knaves. Knights always tell the truth, and knaves always lie.

You meet two inhabitants: Zoey and Mel. Zoey tells you that Mel is a knave. Mel says, “Neither Zoey nor I are knaves.”

Can you determine who is a knight and who is a knave?
"

Statement 
{Zoey Mel : Prop}
(stZ : Zoey ↔ ¬Mel)
(stZn : ¬Zoey ↔ Mel)
(stM : Mel ↔ Mel ∧ Zoey)
  : Zoey ∧ ¬Mel := by
  {
  have hZ : Zoey
  by_contra nZ 
  have hM := stZn.mp nZ
  have hMZ := stM.mp hM
  exact nZ hMZ.right
   
  have nM := stZ.mp hZ
  constructor
  repeat assumption
  }


Conclusion 
"
"
