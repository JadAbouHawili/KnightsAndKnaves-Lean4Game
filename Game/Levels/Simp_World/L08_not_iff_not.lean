import Game.Metadata


World "Simp_World" 
Level 8

Title "" 

Introduction 
"
"

Statement (h : ¬P ↔ ¬Q)
  : P ↔ Q := by

  {
  exact not_iff_not.mp h

  }





Conclusion 
"
"

NewTheorem not_iff_not
