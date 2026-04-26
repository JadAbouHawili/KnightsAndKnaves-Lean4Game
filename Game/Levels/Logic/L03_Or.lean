import Game.MathlibTheorems
import Game.LevelLemmas.Logical

World "Logic"
Level 3

Title "Or, `∨`"

Introduction
"
In this level, we introduce the `∨` logical connective read as 'or'.

You can prove a statement `P ∨ Q` from the fact that `P` is true or `Q` is true. In other words, you
prove an `∨` statement if the left side is true or the right is true.

Therefore, there are two introduction rules for the `∨` symbol. We will however use the `left` and
`right` tactic instead.

You can tell Lean which side of `or` you want to prove by simply executing `left` or `right`.

In our case, we know the left side of `or` (`P`) is true, so use `left`.
"

Statement {P Q: Prop} (hP : P)
  : P or Q := by
{
      left
      Hint "We have a proof that `P` is true, and we want to prove `P`"
      assumption
}

Conclusion
"
Its truth table is as follows:
$
\\begin{array}{|c|c|c|}
\\hline
P & Q & \\text{P or Q} \\\\\\\\
\\hline
T & T & T \\\\\\\\
\\hline
T & F & T \\\\\\\\
\\hline
F & T & T \\\\\\\\
\\hline
F & F & F \\\\\\\\
\\hline
\\end{array}
$

From this truth table, we conclude that to prove `P or Q`, we need either `P` being true or `Q` being true.
"

NewDefinition logic_or
NewTactic left right
