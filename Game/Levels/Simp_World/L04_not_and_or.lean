import Game.Metadata


World "Simp_World"
Level 4

Title "`not_and_or`"

Introduction
"
Notice that `¬(P and Q)`,
$
\\begin{array}{|c | c|c|}
\\hline
P & Q & \\text{¬(P and Q)} \\\\
\\hline
T & T & F \\\\
\\hline
T & F & T \\\\
\\hline
F & T & T \\\\
\\hline
F & F & T \\\\
\\hline
\\end{array}
$

has the same truth table as `¬P or ¬Q`
$
\\begin{array}{|c | c|c|}
\\hline
P & Q & \\text{¬P or ¬Q} \\\\
\\hline
T & T & F \\\\
\\hline
T & F & T \\\\
\\hline
F & T & T \\\\
\\hline
F & F & T \\\\
\\hline
\\end{array}
$

Therefore, they are equivalent and can be interchanged.

On a more intuitive level, we can understand `¬(P and Q)` as meaning `P and Q` is not true, i.e. `P`,`Q` can't be true at the same (at least one of them has to be false)

The simplification theorem to use,
```
not_and_or : ¬(p and q) ↔ ¬p or ¬q
```
"

Statement {P Q : Prop} (h : ¬(P and Q))
  : ¬P or ¬Q := by

  {
  rw [not_and_or] at h
  assumption
  }


Conclusion
"
`simp [not_and_or] at h` instead of `rw [not_and_or] at h` also works.
"
NewTheorem not_and_or
