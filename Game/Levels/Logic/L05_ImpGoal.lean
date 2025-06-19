import Game.Metadata
import Game.LevelLemmas.Logical

World "Logic"
Level 5

Title "Proving an implication, Implication as the goal"

Introduction
"
The goal, translated to English, is: 'If `P` is true, then `P` is true'.

To prove such a goal, we need to assume that `P` is true. Then, we have to prove that `P` is true.

To do this, we need to assume the premise, i.e. introduce it to our assumptions. We can do this using the `intro` tactic. `intro h` will introduce an assumption `h`.
"

Statement {P :Prop}
  : P → P  := by
  {
    intro hP
    Hint
    "
We have a proof of `P` and we want to prove `P`.

`{hP}` exactly matches the goal.
    "
    exact hP
  }

Conclusion
"
The previous two levels showed how to use an implication and how to prove an implication.
"
NewTactic intro
