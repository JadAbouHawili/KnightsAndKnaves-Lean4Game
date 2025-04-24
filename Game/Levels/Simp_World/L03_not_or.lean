import Game.Metadata

World "Simp_World"
Level 3

Title ""

Introduction
"
"
#check not_or
Statement (h : ¬(P or Q))
  : ¬P and ¬Q := by

  {
  rw [not_or] at h
  assumption
  }





Conclusion 
"
"
