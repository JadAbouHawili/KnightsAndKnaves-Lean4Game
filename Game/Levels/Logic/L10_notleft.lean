import Game.Metadata
World "Logic"
Level 10

Title "`notleft_right`"

Introduction 
"
Truth table:
$
\\begin{array}{|c|c|} 
\\hline
P  & False ∨ P \\\\
\\hline
T  & T \\\\
F  & F \\\\
\\hline
\\end{array}
$
Notice that `P`, `False ∨ P` always have the same truth value.

In this level, we have `P ∨ Q` which means that `P` is true or `Q` is true. Since we also know `¬P` i.e `P` is not true, the only option left is `Q` being true.

We will first start by transforming `P ∨ Q` into `False ∨ Q` using `¬P`.

`¬P` means that `P` is False i.e `P = False`.
We have the following theorem:
```
eq_false (h : ¬p) : p = False
```

Use `have` and `eq_false` to get `P = False`.
"

Statement notleft_right {P Q : Prop} (Or : P ∨ Q) (notleft : ¬P) : Q := by
{
  have := eq_false notleft
  Hint "Replace `P` in `Or` with `False`"
  rw [this] at Or
  Hint "
  Since `False ∨ Q` is true, then either `Q` is true or `False` is true. Therefore, `Q` must be true.

  Use the theorem `false_or_iff (p : Prop) : (False ∨ p) ↔ p` to reduce `False ∨ Q` to `Q`.
"
  rw [false_or_iff] at Or
  assumption
}

Conclusion 
"
Instead of doing it manually, you can instead use `simp` tactic.

The `simp` tactic uses lemmas and hypotheses to simplify the main goal target or some assumption.

`simp [notleft] at Or` does the job. It simplifies `Or` using `notleft` and various theorems called 'simp lemmas' , the ones relevant here are `false_or_iff` and `eq_false`.

`simp` will simplify `Or` with the theorems you gave, in this case `notleft : ¬P`. The resulting simplified expression would be `Or : P`.

Not so challenging challenge,
Start off the proof of this goal with:
```
cases Or
```
"

NewTactic «have» simp
NewTheorem false_or_iff eq_false notleft_right
