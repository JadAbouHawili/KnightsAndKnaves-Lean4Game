import Game.Metadata


World "Simp_World" 
Level 7

Title "" 

Introduction 
"
`¬(P ↔ Q)` means that `P` ,`Q` don't have the same truth value i.e one of them is true and the other is false.

truth table here...
"

#check not_iff
Statement (h : ¬(P ↔ Q))
  : ¬P ↔ Q := by

  {
  rw [not_iff] at h
  assumption
  }

Conclusion 
"
Analogous Theorem:
```
not_iff'
```
"
NewTheorem not_iff
