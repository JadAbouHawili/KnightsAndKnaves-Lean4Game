import Game.Metadata

World "Simp_World"
Level 2

Title ""

Introduction
"
`P or Q` to be true requires at least one of `P,Q` to be true.

You have already done this level using `left`/`right` tactic.

Here we introduce a simplification theorem to do it.

But first, rewrite `P or Q` to `True or Q` using
```
eq_true (h : p)
  : p = True
```
"
#check eq_true

Statement (h : P)
  : P or Q  := by

  {
  rw [eq_true h]
  Hint
  "
We can simplify `True or Q` to `Q`

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
`P or Q` is always true for `P = True` i.e `True or Q` and `True` have the same truth value.

$
\\begin\{array}\{|c | c|c|}
\\hline
P & Q & \\text\{P or Q} \\\\
\\hline
T & T & T \\\\
\\hline
T & F & T \\\\
\\hline
\\end\{array}
$

You can use the theorems
```
true_or_iff (p : Prop) : True or p ↔ True
```

or

```
true_or (p : Prop) : (True or p) = True
```
  "
  rw [true_or Q]
  Hint
  "
Now we want to prove `True`. But `True` is always true, so the proof is trivial.

The `trivial` tactic will do the job.
  "
  trivial
}

#check or_true_iff
Conclusion
"
There's an analogous theorem
```
or_true (p : Prop) : (p or True) = True
```

```
or_true_iff (p : Prop) : p or True ↔ True
```

To solve with `simp`,
```
simp [h]
```

Try `simp` before moving on.
"

NewTactic trivial
NewTheorem true_or true_or_iff eq_true
DisabledTactic left right
