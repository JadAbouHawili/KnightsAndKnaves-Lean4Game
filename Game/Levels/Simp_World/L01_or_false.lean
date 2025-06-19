import Game.Metadata

World "Simp_World"

Level 1

Title "`or_false`"

Introduction
"
The simplification here concerns `or`.

We know that either `P` is true or `Q` is true by `h : P or Q`.

We also know that `Q` is false by `hnQ : ¬Q`.

Intution would now say that, given two cases `P` or `Q` and knowing that its not `Q` then it must be `P`. Let's now do this simplification.

We have `¬Q` which means `Q = False`

Rewrite the expression `P or Q` into `P or False` using the theorem
```
eq_false (h : ¬p) : p = False
```
"
#check or_false
#check or_false_iff
Statement {P : Prop} {h : P or Q} {hnQ : ¬Q}
  : P := by
{
  rw [eq_false hnQ] at h
  Hint
  "
After doing so, we get
```
h : P or False
```

We can simplify it to `P` (which is the goal), here's why.

The intution behind every simplifiction introduced can be understood from looking at the truth table of the relevant proposition:


$
\\begin\{array}\{|c | c|c|}
\\hline
P & Q & \\text\{P or Q} \\\\
\\hline
T & T & T \\\\
\\hline
T & F & T \\\\
\\hline
F & T & T \\\\
\\hline
F & F & F \\\\
\\hline
\\end\{array}
$

Notice that for `Q = False`,
$
\\begin\{array}\{|c | c|c|}
\\hline
P & Q & \\text\{P or Q} \\\\
\\hline
T & F & T \\\\
\\hline
F & F & F \\\\
\\hline
\\end\{array}
$

`P or Q` has the same truth value as `P`.(for `Q = False`)

In other words, `P or False` and `P` have the same truth value i.e `(P or False) ↔ P`. Whenver `P or False` occurs, we can replace it by `P` which is of a simpler form.
$
\\begin\{array}\{|c|c|}
\\hline
P & \\text\{P or False} \\\\
\\hline
T & T \\\\
\\hline
F & F \\\\
\\hline
\\end\{array}
$

The theorem for this simplication
```
or_false_iff (p : Prop)
: p or False ↔ p
```

There's also an equivalent
```
or_false (p : Prop)
: (p or False) = p
```

Rewrite  at `h : P or False` obtaining `h : P`, using the theorem `or_false` or `or_false_iff`.
  "
  rw [or_false_iff P] at h
  assumption
}

Conclusion
"
You can also simplify `h` using the `simp` tactic.(which stands for simplification)

We want to simplify `h` using `hnQ`, so
```
simp [hnQ] at h
```
will do.

Try it.
"

NewTheorem eq_false or_false_iff or_false
NewTactic simp
