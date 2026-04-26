import Game.MathlibTheorems
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
  : P → P := by
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


# Truth table
$
\\begin{array}{|c|c|c|}
\\hline
P & Q & P → Q \\\\\\\\
\\hline
T & T & T \\\\\\\\
\\hline
T & F & F \\\\\\\\
\\hline
F & T & T \\\\\\\\
\\hline
F & F & T \\\\\\\\
\\hline
\\end{array}
$

A statement `P → Q` is false when `P` is true and `Q` false, it's true otherwise.
This is because this is the only case where the meaning of `P → Q` is violated, i.e. we have that `P` is true so `Q` is supposed to be true as well but it's not.

When `P` is false, the implication `P → Q` is always true regardless of the truth value of `Q`. That's because the implication does not tell us what `Q` should be when `P` is false -- it only tells us that `Q` must be true when `P` is true.


"
NewTactic intro
