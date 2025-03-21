import Game.Metadata
import Game.LevelLemmas.Logical

World "Logic"
Level 6

Title ""

Introduction 
"
In this level, we will do a 'proof by cases'. 
By `h : P or Q`, we have two cases:
`P` being true or `Q` being true. If we consider each case individually and prove `R`, then we can conclude that `R` is true.

To do this, start with `cases h`
"

Statement 
{P Q R : Prop}
(h : P or Q)
(hPR : P → R)
(hQR : Q → R)
  : R := by

  {
  cases h
  exact hPR h_1
  exact hQR h_1
  }

Conclusion
"
"

NewTactic cases
