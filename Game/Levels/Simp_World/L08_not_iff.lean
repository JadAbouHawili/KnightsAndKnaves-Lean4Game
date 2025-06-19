import Game.Metadata


World "Simp_World"
Level 8

Title "`not_iff`"

Introduction
"
`¬(P ↔ Q)` means that `P` ,`Q` don't have the same truth value i.e. one of them is true and the other is false.

Here are the values for `P`,`Q` where `¬(P ↔ Q)` is satisfied:
$
\\begin{array}{|c | c|c|}
\\hline
P & Q & \\text{¬(P ↔ Q)} \\\\
\\hline
T & F & T \\\\
\\hline
F & T & T \\\\
\\hline
\\end{array}
$

We can conclude that `¬P`,`Q` have the same truth value (`¬P ↔ Q`) and `P`,`¬Q` have the same truth value (`P ↔ ¬Q`).

The theorem for the former simplification:
```
not_iff : ¬(a ↔ b) ↔ (¬a ↔ b)
```
"

Statement (h : ¬(P ↔ Q))
  : ¬P ↔ Q := by

  {
  rw [not_iff] at h
  assumption
  }

Conclusion
"
Analogous Theorem:
```
not_iff' : ¬(P ↔ Q) ↔ (P ↔ ¬Q)
```
"

NewTheorem not_iff not_iff'
