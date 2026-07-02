import Game.MathlibTheorems

World "EquationalReasoning"
Level 2

Title "`exact`, goal is true by assumption"

Introduction
"
In this level, we have `Objects`, `Assumptions`, and the `Goal`.

# Objects
`x : ℕ` means `x` is of type `ℕ`(natural number).
In other words , `x` is a `ℕ`.

# Assumptions
In our assumptions , we specify properties about our objects.

`x = 2` is a proposition(`x = 2 : Prop`). We have `h : x = 2` which means that `h` is of type `x =
  2` i.e a proof of the proposition `x = 2`.

# Goal
Our goal is to prove `x = 2`.

We already have a proof `h : x = 2`

`exact h` tells Lean that `h` is EXACTLY what's needed to prove/close the goal.
"

Statement {x : ℕ} (h : x=2)
  : x=2 := by
  {
    exact h
  }

Conclusion
"
The `assumption` tactic tries to prove the goal using one of the assumptions

Try it before moving on to the next level. Just type `assumption` instead of `exact h`
"

NewTactic exact assumption
NewDefinition Nat
