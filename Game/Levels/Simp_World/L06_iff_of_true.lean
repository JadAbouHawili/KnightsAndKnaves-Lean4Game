import Game.Metadata


World "Simp_World" 
Level 6

Title "iff_of_true" 

Introduction 
"
"

Statement (hP : P) (hQ : Q)
  : P ↔ Q := by

  {
  exact iff_of_true hP hQ
  }

Conclusion
"
"
NewTheorem iff_of_true
