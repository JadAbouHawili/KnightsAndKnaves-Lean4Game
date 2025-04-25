import Game.Metadata


World "Simp_World" 
Level 1

Title "`simp` tactic"

Introduction 
"
The simplification here concerns `or`.

First, we have `¬Q` which means `Q = False`

Rewrite the expression `P or Q` into `P or False` using the theorem
```
eq_false (h : ¬p) : p = False
```


After doing so , we have
```
h : P or False
```

We can simplify it to `P`, here's why.

The intution behind every simplifiction introduced can be understood from looking at the truth table of the relevant proposition:
$
\\begin{array}{|c c|c|}
\\hline
P & Q & P or Q \\\\
\\hline
T & T & T \\\\
\\hline
T & F & T \\\\
\\hline
F & T & T \\\\
\\hline
F & F & F \\\\
\\hline
\\end{array}
$

Notice that for `Q = False`, `P or Q` is has the same truth value as `P`.

In other words, `P or False` and `P` have the same truth value i.e `(P or False) ↔ P`. Whenver `P or False` occurs , we can replace it by `P` which is of a simpler form.
$
\\begin{array}{|c c|c|}
\\hline
P & P or False \\\\
\\hline
T & T \\\\
\\hline
F & F \\\\
\\end{array}
$

The theorem for this simplication
```
or_false_iff (p : Prop) : p or False ↔ p
```

There's also an equivalent
```
or_false (p : Prop) : (p or False) = p
```

Rewrite `P or False` at `h` with `P` using the theorem `or_false` or `or_false_iff`.
"
#check or_false
#check or_false_iff
Statement {P : Prop} {h : P or Q} {hnQ : ¬Q}
  : P := by
  {
  rw [eq_false hnQ] at h
  rw [or_false_iff P] at h
  assumption
  }

Conclusion 
"
"
NewTheorem eq_false or_false_iff or_false
