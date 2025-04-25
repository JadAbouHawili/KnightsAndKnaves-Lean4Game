import Game.Metadata


World "Simp_World" 
Level 2

Title ""

Introduction
"
Previously, the way to prove this was using the `left`/`right` tactic which was accompanied with an intuitive explanation on why `left`/`right` make sense.

Here we introduce a simplification theorem to do it.

But first, rewrite `P or Q` to `True or Q`
"

Statement (h : P)
  : P or Q  := by

  {
  rw [eq_true h]
  Hint
  "
Now use
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
Now we want to prove `True`. But `True` is true, so the proof is trivial. 

The `trivial` tactic will do the job
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
"

NewTactic trivial
NewTheorem true_or true_or_iff eq_true
