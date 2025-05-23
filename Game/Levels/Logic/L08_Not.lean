import Game.Metadata
import Game.LevelLemmas.Logical

World "Logic"
Level 8

Title "Not Connective, ¬"

Introduction
"
In this level we introduce the negation, the `¬` connective (read as 'not').

Notice that this is the first logical connective that applies on one proposition only and not two.

The job of this connective(as the name implies), is to negate a proposition:
- For `P` true, `¬P` is false.
- For `P` false, `¬P` is true.

In truth table form:
$
\\begin{array}{|c|c|} 
\\hline
P & ¬P \\\\
\\hline
T & F \\\\
F & T \\\\
\\hline
\\end{array}
$

Notice that since `P` is true, `¬P` should be false but in this proof state it is true (by `hnP`). This is a contradiction. The goal is to prove `False` which means to prove a contradiction.

Note that we don't need to introduce a new symbol to define negation, it can be defined in terms of what we already know.

Consider the following truth table: 
$
\\begin{array}{|c|c|} 
\\hline
P & P → False \\\\
\\hline
T & F  \\\\
F & T  \\\\
\\hline
\\end{array}
$

Notice that regardless of the truth value of `P`, the two propositions `¬P` and `P → False` have the same truth table. Therefore, they can be used interchangeably.(we say that these two expressions are logically equivalent, `¬P ↔ (P → False)`)

What `¬P` means is that if `P` were true, then we can deduce a contradiction. We know that `P` is true. Therefore, we can prove a contradiction which is the goal.

To see `¬P` in its implication form, you can do `unfold Not` to unfold the definition of `¬`. Note that this would apply to the goal, and so `unfold Not at hnP` applies at `hnP`.

"

#check not_of_eq_false
Statement {P: Prop}
{hP : P} {hnP : ¬P}
: False := by{
    Hint (hidden:=true)
   "Remember that an implication acts like a function, that takes a proof of whats on the left hand returning a proof of whats on the right hand side.

For this level, `¬P` being true tells us that a proof of `P` gives us a proof of `False`. We have a proof of `P`. Therefore we can obtain a proof of `False` which is the goal."
    unfold Not at hnP

    Hint (hidden:=true)
   "Remember that an implication acts like a function, that takes a proof of whats on the left hand returning a proof of whats on the right hand side.

For this level, `¬P` being true tells us that a proof of `P` gives us a proof of `False`. We have a proof of `P`. Therefore we can obtain a proof of `False` which is the goal."
    exact hnP hP
 }

Conclusion 
"
In the next level, we will explore what it means to have proven `False`.
"

NewTactic unfold
NewDefinition Not
