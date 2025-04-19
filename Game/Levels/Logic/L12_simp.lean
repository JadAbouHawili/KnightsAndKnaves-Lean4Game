import Game.Metadata


World "Logic" 
Level 12 

Title "simp"

Introduction 
"
In the upcoming levels, we will introduce simplications of propositions.

The simplification here concerns `or`.

The intution behind the simplifiction can be understood from looking at the truth table which we put here for reference:
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

Notice that for `Q = False`, `P or Q` is true regardless of what `P` is.

In other words, `P or False` and `P` have the same truth value i.e `(P or False) ↔ P`. Whenver `P or False` occurs , we can replace it by `P`.

You learned how to do this from the `↔` levels.

The theorem for this simplication
```
or_false_iff (p : Prop) : p or False ↔ p
```

However, `simp` would apply such a simplification without you having to reference the theorem and use `rw`.

Apply `simp` at `h` , i.e `simp at h`.
"
#check or_false
#check or_false_iff
Statement {P : Prop} {h : P or False}
  : P := by

  {
  simp at h
  assumption
  }

Conclusion 
"
"
NewTactic simp
