import Game.MathlibTheorems
import Game.LevelLemmas.Logical

World "Logic"
Level 9

Title "Not Connective, ¬"

Introduction
"
In this level we introduce logical negation, the `¬` connective (read as 'not').

Notice that this is the first logical connective that applies on one proposition only and not two.

The job of this connective (as the name implies) is to negate a proposition:
- For `P` true, `¬P` is false.
- For `P` false, `¬P` is true.

First , unfold the definition of `¬` by doing `unfold Not at hnP`
"

#check Not.intro
Statement {P: Prop}
{hP : P} {hnP : ¬P}
: False := by{
    unfold Not at hnP

    Hint
    "
`¬P` is defined as `P → False` which means if `P` were true, then we can deduce a contradiction.

We have a proof of `P` so we can prove the goal `False`(a contradiction)
"
    Hint (hidden:=true)
   "Remember that an implication acts like a function, that takes a proof of whats on the left hand returning a proof of whats on the right hand side.
   "
    exact hnP hP
 }

Conclusion
"
In the next level, we will explore what it means to have proven `False`, and what it means to have
contradictory assumptions in our proof state.

Why `¬P` is defined as `P → False` and does this match our intuition of what negation should be?


In truth table form, this is what the behavior of `¬P` should be:
$
\\begin{array}{|c|c|}
\\hline
P & ¬P \\\\\\\\
\\hline
T & F \\\\\\\\
F & T \\\\\\\\
\\hline
\\end{array}
$

We will show that `P → False` behaves the same way


Consider the `→` truth table:
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

Let's focus on the rows where `Q=False`,
$
\\begin{array}{|c|c|}
\\hline
P & P → False \\\\\\\\
\\hline
T & F \\\\\\\\
\\hline
F & T \\\\\\\\
\\hline
\\end{array}
$

Notice that regardless of the truth value of `P`, the two propositions `¬P` and `P → False` have
the same truth table. Therefore, they can be used interchangeably and essentially have the same
meaning i.e are logically equivalent (`¬P ↔ P → False`).
"

NewTactic unfold
NewDefinition Not
