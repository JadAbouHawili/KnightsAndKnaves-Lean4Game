import Game.Metadata

World "Simp_World"
Level 3

Title ""

Introduction
"
Notice that `¬(P or Q)`,
$
\\begin{array}{|c | c|c|}
\\hline
P & Q & \\text{¬(P or Q)} \\\\
\\hline
T & T & F \\\\
\\hline
T & F & F \\\\
\\hline
F & T & F \\\\
\\hline
F & F & T \\\\
\\hline
\\end{array}
$

has the same truth table as `¬P and ¬Q`
$
\\begin{array}{|c | c|c|}
\\hline
P & Q & \\text{¬P and ¬Q} \\\\
\\hline
T & T & F \\\\
\\hline
T & F & F \\\\
\\hline
F & T & F \\\\
\\hline
F & F & T \\\\
\\hline
\\end{array}
$

Therefore, they are equivalent and can be interchanged.

On a more intuitive level, we can understand `¬(P or Q)` as meaning .... 
"

#check not_or
Statement (h : ¬(P or Q))
  : ¬P and ¬Q := by
  {
  rw [not_or] at h
  assumption
  }

Conclusion
"
"
NewTheorem not_or
