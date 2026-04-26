import Game.MathlibTheorems
import Game.LevelLemmas.Logical

World "Logic"
Level 2

Title "And, `∧`"
Introduction
"
In this level, we introduce the `∧` logical connective (read as 'and').

Given the following proofs that `x = 2` and `y = 6`,
```
h : x = 2
h' : y = 6
```
we can construct a proof that `x = 2 AND y = 6` written in Lean notation as `x = 2 ∧ y = 6`.

We construct such an expression using an introduction rule called `And.intro` which introduces the `∧` symbol
```
And.intro (hP : P)
          (hQ : Q)
: P and Q
```

You can think of `And.intro` as a function that takes two inputs: a proof of `P`, a proof of `Q` and returns a proof of `P and Q`.

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
Logical connectives are either defined by their introduction and elimination rules or by truth
tables.

An introduction rule 'introduces' a symbol , in this case proving a statement of `and`.

An elimination rule 'eliminates' a symbol extracting information from it. For an expression `P and Q`
, applying the elimination rule would give you a proof of `P` and a proof of `Q` separately.(seen in future levels)

The only way to introduce the symbol `∧` i.e prove a statement involving `∧` is to use the
`And.intro` introduction rule which requires a proof of `P` and a proof of `Q`.

We can conclude from this that `P ∧ Q` is true in only one case: when `P` is true and `Q` is true. It is false otherwise

In truth table form, this looks like:

`T` stands for true
`F` stands for false

$$
\\begin{array}{|c|c|c|}
\\hline
x=2 & y=6 & x=2 ∧ y=6 \\\\\\\\
\\hline
T & T & T \\\\\\\\
\\hline
T & F & F \\\\\\\\
\\hline
F & T & F \\\\\\\\
\\hline
F & F & F \\\\\\\\
\\hline
\\end{array}
$$

Restart the level and use these two alternative techniques to solve it:
- You can also use the `constructor` tactic which will split the goal `P and Q` into two, the first being to prove `P` and the second being to prove `Q`.
- Moreover, instead of `And.intro hP hQ` you can use the notation `\\<hP,hQ\\>` which means the same thing.
"

NewTheorem And.intro
NewDefinition logic_and
NewTactic constructor
