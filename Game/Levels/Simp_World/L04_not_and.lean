import Game.Metadata


World "Simp_World" 
Level 4

Title "" 

Introduction 
"
"

Statement (h : ¬(P and Q))
  : ¬P or ¬Q := by

  {
  rw [not_and_or] at h
  assumption
  }





Conclusion 
"
"
