import Game.Metadata
import Game.LevelLemmas.Logical

World "Logic"
Level 2

Title "And, `∧`"
Introduction
"
In this level, we introduce the `∧` logical connective (read as 'and').

Remember the following example:
Given the two propositions `x=2` (`P`), `y=6` (`Q`), we can construct a new propositon `x=2 ∧ y=6` (`P ∧ Q`) which is read as `x=2 and y=6` (`P and Q`).

What is the truth value of this new proposition `x=2 ∧ y=6` (`P ∧ Q`)?
Well, it would depend on the truth value of the two component propositions `x=2` (`P`), `y=6` (`Q`).

What possibilities are there for each's truth value? `x=2` (`P`) can either be true or false and similarly for `y=6` (`Q`). Here is a truth table that goes through all these possibilities:
`T` stands for true
`F` stands for false
$
\\begin{array}{|c|c|c|}
\\hline
x=2 & y=6 & x=2 ∧ y=6 \\\\
\\hline
T & T & T \\\\
\\hline
T & F & F \\\\
\\hline
F & T & F \\\\
\\hline
F & F & F \\\\
\\hline
\\end{array}
$


The proposition `x=2 and y=6` (`P and Q`) is true when `x=2` (`P`) is true AND `y=6` (`Q`) is true.
In other words, if `P` is true AND `Q` is true regardless of what proposition `P` stands for, `Q` stands for. The only thing that matters is their truth value.
Therefore, the more general truth table is the same:
$
\\begin{array}{|c|c|c|}
\\hline
P & Q & P ∧ Q \\\\
\\hline
T & T & T \\\\
\\hline
T & F & F \\\\
\\hline
F & T & F \\\\
\\hline
F & F & F \\\\
\\hline
\\end{array}
$

Notice that `P and Q` is true when both `P` is true and `Q` is true, being false otherwise.

From this, we conclude that we can prove `P and Q` if we have a proof of `P` and a proof of `Q`.

This is called the `and` introduction rule `And.intro`:
```
And.intro  (left : P)
           (right : Q)
: P and Q
```

You can think of `And.intro` as a function that takes two inputs: a proof of `P`, a proof of `Q` and returns a proof of `P and Q`.

For example:
```
And.intro arg1 arg2
```
where `arg1 : P`, `arg2 : Q`, `(And.intro arg1 arg2) : P and Q`.

Use it to construct an object of type `P and Q`, and use `exact` to close the goal.
"

Statement (P Q : Prop) (hP : P) (hQ : Q)
  : P and Q  := by
  {
    Hint(hidden:=true)
    "
exact And.intro hP hQ
    "
    exact And.intro hP hQ
  }

Conclusion
"
You can also use the `constructor` tactic which will split the goal `P and Q` into two,
the first being to prove `P` and the second being to prove `Q`.

Moreover, instead of `And.intro hP hQ` you can use the notation `\\<hP,hQ\\>` which means the same thing.
"

NewTheorem And.intro
NewDefinition logic_and
NewTactic constructor
