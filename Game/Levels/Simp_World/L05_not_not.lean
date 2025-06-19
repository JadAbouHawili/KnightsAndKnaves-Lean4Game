import Game.Metadata


World "Simp_World"
Level 5

Title "`by_contra`, `not_not`"

Introduction
"
In this level, you will learn 'proof by contradiction'.

To prove `P`, you would assume `¬P` and then prove false, i.e. you would be proving `¬P → False` which is `¬¬P`.

The truth table shows that `¬¬P` is equivalent to `P`,
$
\\begin{array}{|c | c|c|}
\\hline
P & ¬P & \\text{¬¬P}\\\\
\\hline
T & F & T \\\\
\\hline
F & T & F \\\\
\\hline
\\end{array}
$

There are two ways to solve this level, and you should try both.

The first way is using the simplification theorem (to simplify `¬¬P` to `P`),
```
not_not : ¬¬a ↔ a
```

The second is using the `by_contra` tactic where `by_contra h` would be assuming `h : ¬P`.
"

Statement
{P : Prop}
{hP : ¬¬P}
  : P := by

  {
  by_contra h
  contradiction
  }

Conclusion
"
`simp at hP` simplifies `hP : ¬¬P` into `hP : P`

You don't have to do `simp [not_not] at hP` because `not_not` is marked as a `@simp` lemma.
"
#check not_not
NewTactic by_contra
NewTheorem Classical.not_not
