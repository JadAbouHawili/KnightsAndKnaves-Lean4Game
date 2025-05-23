import Game.Metadata
import Game.LevelLemmas.Logical

World "Logic"
Level 3

Title "Or, `∨`"

Introduction
"
In this level, we introduce the `∨` logical connective read as 'or'.

Its truth table is as follows:
$
\\begin{array}{|c|c|c|}
\\hline
P & Q & \\text{P or Q} \\\\
\\hline
T & T & T \\\\
\\hline
T & F & T \\\\
\\hline
F & T & T \\\\
\\hline
F & F & F \\\\
\\hline
\\end{array}
$

From this truthtable, we conclude that to prove `P or Q`,  we need either `P` being true or `Q` being true (both being true would also mean its true).

You can tell Lean which side of `or` you want to prove by simply executing `left` or `right`.

In our case, we know the left side of `or`(`P`) is true, so use `left`.
"

#check Or.inl
#check Or.intro_right
Statement (hP : P)
  : P or Q  := by
{
      left
      Hint "We have a proof that `P` is true, and we want to prove `P`"
      assumption
}

Conclusion
"
"

NewDefinition logic_or
NewTactic left right
