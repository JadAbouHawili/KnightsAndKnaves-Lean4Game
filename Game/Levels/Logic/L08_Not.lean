import Game.MathlibTheorems
import Game.LevelLemmas.Logical

World "Logic"
Level 8

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

Statement {P: Prop}
{hP : P} {hnP : ¬P}
: False := by{
    unfold Not at hnP

    Hint
    "
What `¬P` means is that if `P` were true, then we can deduce a contradiction. We know that `P` is true. Therefore, we can prove a contradiction which is the goal.

`¬P` is defined as `P → False`. We have a proof of `P` so we can prove `False`(a contradiction)

`¬P` being true tells us that a proof of `P` gives us a proof of `False`. We have a proof of `P`. Therefore we can obtain a proof of `False` which is the goal.
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

But for now , let's talk about why `¬P` is defined as `P → False`.


In truth table form:
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
meaning (we say that these two expressions are logically equivalent, `¬P ↔ (P → False)`).
"

NewTactic unfold
NewDefinition Not
