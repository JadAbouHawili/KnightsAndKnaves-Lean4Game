import Game.MathlibTheorems
import Game.LevelLemmas.Logical

World "Logic"
Level 4

Title "Implication, →"

Introduction
"
In this level, we introduce the logical implication `→` connective.
Logical implication `P → Q` is made up of two components:
- The premise, which in this case is `P`
- The conclusion, which in this case is `Q`

`P → Q` is read as 'If `P` is true, then `Q` is true'.
`P` being true IMPLIES `Q` being true. A proof of `P` IMPLIES a proof of `Q`.

In the current proof state, we know `P` and we know `P → Q`. Therefore, we can conclude `Q`.

You can think of logical implication as a function. `P → Q` takes a proof of `P` and returns a proof of `Q`.

Pass `hP` as an argument to `PtoQ` getting a proof of `Q`.

You can then use `exact` to close the goal
"
Statement {P Q : Prop}  (hP : P) (PtoQ: P → Q) : Q := by
  Hint(hidden := true)
  "
`PtoQ hP`, this is exactly whats needed to prove the goal.
  "
  exact PtoQ hP

Conclusion
"

In the next level, you will learn how to prove an implication using the `intro` tactic.
"
NewDefinition imp
