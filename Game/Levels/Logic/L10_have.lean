import Game.Metadata

World "Logic" 
Level 10

Title "`have`" 

Introduction 
"
In this level, we introduce that `have` tactic. 
You have to prove `R` but to you need `Q` first. 

Use `have hQ : Q` to change the goal to proving `Q`.
"

Statement {P Q R : Prop}
{hP : P}
{hPQ : P → Q}
{hQR : Q → R}
  : R := by

  {
  have hQ : Q
  Hint
  "
  `hPQ` takes `hP` and gives you a proof of `Q`
  "
  exact hPQ hP

  Hint
  "
Now that you proved `Q`,

`hQR` takes `{hQ}` and gives you a proof of `R` which is the goal.
  "
  exact hQR hQ
  }

Conclusion
"
"
NewTactic «have»
