import Game.Metadata


World "Simp_World" 
Level 5

Title "iff_of_false" 

Introduction 
"
"

Statement (hnP : ¬P) (hnQ : ¬Q)
  : P ↔ Q := by

  {
  exact iff_of_false hnP hnQ
  }

Conclusion
"
"
NewTheorem iff_of_false
