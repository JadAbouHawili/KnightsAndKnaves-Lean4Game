import Game.Metadata

World "EquationalReasoning"
Level 2

Title "`exact`, goal is true by assumption"

Introduction
"
In this level, we have `Objects`, `Assumptions`, and the `Goal`.

# Objects
Objects will always be variables (letter symbols) we are working with. What these variables denote is specified after the `:`, what is after the `:` is called the type of the object.

Here, `x` denotes a number but we don't know which number it is. The `: ℕ` in `x : ℕ` means that `x` is a natural number (positive numbers like `1`,`2`,`3`, and so on...).

# Assumptions
As for the assumptions, we have `h : x=2` which means that `h` is an object of type `x=2`. This essentially means that `h` is an object asserting that the proposition (or statement) `x=2` is true. In other words, we know that `x=2` and `h` is a proof of that.

# Goal
Our goal is to prove that `x = 2`.
We must use our assumptions.
We have that `h : x=2`, i.e. `h` is a proof that `x=2`.

`h` is a proof of our goal, we should let `Lean` know that we have a proof of the goal. Using `exact h` accomplishes this because `h` is EXACTLY the goal.
"

Statement{x : ℕ} (h : x=2)
  : x=2 := by
  {
    exact h
  }

Conclusion
"
The `exact` in `exact h` tells `Lean` that `h`'s type EXACTLY matches the goal. In other words, `h` is EXACTLY what we need to prove the goal. `Lean` verifies this and reports that there are no more goals to prove. We are done.

The `assumption` tactic can also be used here which searches for an assumption that matches the goal, and closes the goal if it finds one.

Try it before moving on to the next level.
"

NewTactic exact assumption
NewDefinition Nat
