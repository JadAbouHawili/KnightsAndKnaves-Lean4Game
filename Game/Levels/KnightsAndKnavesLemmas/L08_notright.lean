import Game.Metadata

World "KnightsAndKnavesLemmas" 
Level 8

Title "`notright_left`" 

Introduction
"
In this level, we have `P ∨ Q` which means that `P` is true or `Q` is true. Since we also know `¬Q` i.e `Q` is not true, the only option left is `P` being true.

We will first start by transforming `P ∨ Q` into `P ∨ False` using `¬Q`.

`¬Q` means that `Q` is False i.e `Q = False`.
We have the following theorem:
```
eq_false (h : ¬p) : p = False
```

Use `have` and `eq_false` to get `Q = False`.

"

#check or_iff_not_imp_left
#check or_iff_not_imp_right
Statement {P Q : Prop} (Or : P ∨ Q) (notright : ¬Q) (hPF : P ∨ False → P) : P := by
{
  have := eq_false notright
  Hint "Replace `Q` in `Or` with `False`"
  rw [this] at Or
  Hint "
  Since `P ∨ False` is true, then either `P` is true or `False` is true. Therefore, `P` must be true.

Use `or_false_iff (p : Prop) : (p ∨ False) ↔ p` to reduce `Or : P ∨ False` to `Or : P` , then use `Or : P` to prove the goal.
  "
  rw [or_false_iff] at Or
  assumption
}
#check or_false_iff

Conclusion 
"
Instead of doing it manually, you can instead use `simp` tactic.

The `simp` tactic uses lemmas and hypotheses to simplify the main goal target or some assumption.

`simp [notright] at Or` does the job. It simplifies `Or` using `notright` and various theorems called 'simp lemmas' , the ones relevant here are `or_false_iff` and `eq_false`.

`simp` will simplify `Or` with the theorems you gave, in this case `notright : ¬Q`. The resulting simplified expression would be `Or : P`.
"

NewTheorem notright_left eq_false or_false_iff
