import Game.Metadata

World "Logic"
Level 10

Title "`have`"

Introduction
"
In this level, we introduce the `have` tactic.
You have to prove `R` but to do that, you need `Q` first.

Use `have hQ : Q` to change the goal to proving `Q`. And when the proof is done, it would be named `hQ` and added to the assumptions in the proof state.
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
Now that you proved `Q`, its proof `{hQ} : Q` has been added to the assumptions.

`hQR` takes `{hQ}` and gives you a proof of `R` which is the goal.
  "
  exact hQR hQ
  }

Conclusion
"
`have h : P` changes the goal to proving `P` and adds the proof `h` after that goal is closed.
"

NewTactic «have»
