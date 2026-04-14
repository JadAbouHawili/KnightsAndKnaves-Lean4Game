import Game.MathlibTheorems

World "EquationalReasoning"
Level 2

Title "`exact`, goal is true by assumption"

Introduction
"
In this level, we have `Objects`, `Assumptions`, and the `Goal`.

# Objects
`x : ℕ` means `x` is of type `ℕ`(natural number).
In other orders , `x` is a `ℕ`.

`x` denotes a number but we don't know which number it is.(yet)

# Assumptions
In our assumptions , we specify properties about our objects.

We have `h : x = 2` which means that `h` is of type `x = 2`. This essentially means that `h` is
a proof that `x = 2`. What is the type of `x=2`? Well , `x=2 : Prop` which means `x = 2` is a proposition. This is the prposoitions as
types and proofs as terms perspective which you can read about here...

# Goal
Our goal is to prove that `x = 2`.
We must use our assumptions.
We have that `h : x = 2`, i.e. `h` is a proof that `x = 2`.

Looks like we are ready to prove/close the goal.
`exact h` tells Lean that `h` is EXACTLY what's needed to prove/close the goal.
"

Statement{x : ℕ} (h : x=2)
  : x=2 := by
  {
    exact h
  }

Conclusion
"
The goal is asking for an object of type `x = 2`.
The `exact` in `exact h` tells `Lean` that `h`'s type EXACTLY matches the goal. In other words, `h` is EXACTLY what we need to prove the goal. `Lean` verifies this and reports that there are no more goals to prove. We are done.

The `assumption` tactic can also be used here which searches for an assumption that matches the goal, and closes the goal if it finds one.

Try it before moving on to the next level. Just type `assumption` instead of `exact h`
"

NewTactic exact assumption
NewDefinition Nat
