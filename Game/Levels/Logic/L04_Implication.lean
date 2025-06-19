import Game.Metadata
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

# truth table
$
\\begin{array}{|c|c|c|} 
\\hline
P & Q & P → Q \\\\
\\hline
T & T & T \\\\
\\hline
T & F & F \\\\
\\hline
F & T & T \\\\
\\hline
F & F & T \\\\
\\hline
\\end{array}
$

A statement `P → Q` is false when `P` is true and `Q` false, it's true otherwise.
This is because this is the only case where the meaning of `P → Q` is violated i.e we have that `P` is true so `Q` is supposed to be true as well but its not.

When `P` is false, the implication `P → Q` is always true regardless of the truth value of `Q` because the implication does not tell us what `Q` should be when `P` is false, it only tells us that `Q` must be true when `P` is true.

In the current proof state, we know `P` (i.e `P` is true), and we know `P → Q` (i.e `P → Q` is true). Therefore, we can conclude `Q` (i.e `Q` is true ).

You can think of logical implication as a function with one input and one output. It takes a proof of `P` and returns a proof of `Q`.

Give `ptoq : P → Q` the proof `hP : P` to get a proof of `Q`.

You can then use `exact` to close the goal
"
Statement {P Q : Prop}  (hP : P) (ptoq: P → Q) : Q := by
  Hint(hidden := true)
  "
`ptoq hP : Q`, this is exactly whats needed to prove the goal.
  "
  exact ptoq hP

Conclusion
"
In the next level, you will learn how to deal with an implication as the goal you have to prove.
"
NewDefinition imp
