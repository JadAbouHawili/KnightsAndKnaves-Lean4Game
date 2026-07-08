import Game.MathlibTheorems

World "Simp_World"
Level 3

Title "`not_or`"

Introduction
"
Notice that `¬(P or Q)`
$
\\begin{array}{|c | c|c|}
\\hline
P & Q & \\text{¬(P or Q)} \\\\\\\\
\\hline
T & T & F \\\\\\\\
\\hline
T & F & F \\\\\\\\
\\hline
F & T & F \\\\\\\\
\\hline
F & F & T \\\\\\\\
\\hline
\\end{array}
$

has the same truth table as `¬P and ¬Q`

$
\\begin{array}{|c | c|c|}
\\hline
P & Q & \\text{¬P and ¬Q} \\\\\\\\
\\hline
T & T & F \\\\\\\\
\\hline
T & F & F \\\\\\\\
\\hline
F & T & F \\\\\\\\
\\hline
F & F & T \\\\\\\\
\\hline
\\end{array}
$

Therefore, they are equivalent and can be interchanged.

On a more intuitive level, we can understand `¬(P or Q)` as meaning `P or Q` is not true, i.e. it
is not true that either `P` or `Q` is true, i.e. `P` is false and `Q` is false (`¬P ∧ ¬Q`).

The simplification theorem to use,
```
not_or : ¬(p or q) ↔ ¬p and ¬q
```
"

Statement {P Q : Prop} (h : ¬(P or Q))
  : ¬P and ¬Q := by
  {
  Hint (hidden := true)
  "
```
rw [not_or] at h
```

or

```
exact not_or.mp h
```
  "
  rw [not_or] at h
  assumption
  }

Conclusion
"
"

NewTheorem not_or
