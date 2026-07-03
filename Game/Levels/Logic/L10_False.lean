import Game.MathlibTheorems
import Game.LevelLemmas.Logical

World "Logic"
Level 10

Title "From `False`, anything follows."

Introduction
"
We proved `False`, what does this mean? What can we conclude? What does `False` IMPLY?

Let's check the `→` truth table:
$$
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
$$

Let's focus on part of the truth table where `P` is `False`, because we want to see what `False` implies.
$$
\\begin{array}{|c|c|c|}
\\hline
Q & False → Q \\\\\\\\
\\hline
T & T \\\\\\\\
\\hline
F & T \\\\\\\\
\\hline
\\end{array}
$$

We have that the implication `False → Q` is true for any proposition `Q`. From `False` , anything follows.

This principle is represented by [#False.elim](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#False.elim)) proves any proposition `Q`.

The `contradiction` tactic exemplifies this principle and its what we will use in this game. Just type
`contradiction`
"
Statement {Q : Prop} (hF : False) : Q := by
  contradiction

Conclusion
"
"

NewTactic contradiction
NewDefinition False
