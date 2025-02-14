import Game.Metadata

World "KnightsAndKnavesLemmas"
Level 7

Title "If you're not a knave, then the only option left is a knight."

Introduction 
"
You are either a knight or a knave. If you are not a knave, then the only option left is being a knight.

In this level, we know:
```
A ∈ Knight ∨ A ∈ Knave
A ∉ Knave
```
and want to prove:
```
A ∈ Knight
```

In other words, we know that the right side of `∨` is not true and we want to prove the left side. This is a job for `notright_left`.

"
/-
You are either a knight or a knave (`h`). If you are not a knave (`h'`), then the only option left is being a knight.

In this level, we know:
```
A ∈ Knight ∨ A ∈ Knave
A ∉ Knave
```
In our case, `P` is `A ∈ Knight`. Since we know `A ∉ Knave` then we can say that `A ∈ Knave = False`. Replacing this in the `∨` expression gives us `A ∈ Knight ∨ False`.

In other words, we have that `A ∈ Knight ∨ False` is true. So we must have `A ∈ Knight`.
-/

Statement
{Knight : Finset Inhabitant } {Knave : Finset Inhabitant}
{inst : DecidableEq Inhabitant}
(h' : ¬ (A ∈ Knave))
(h'' : A ∈ Knight ∨ A ∈ Knave)
  :  A ∈ Knight := by
{
  exact notright_left h'' h'
}

Conclusion
"
Let's recap what we have proven.

Given the following proof state:
```
(Knight : Finset K ) (Knave : Finset K)
(h : Knight ∩ Knave = ∅ )
(h'' : A ∈ Knight ∨ A ∈ Knave)
```

We can conclude the following implications:
A ∈ Knight → A ∉ Knave (using `h`) 
A ∉ Knave → A ∈ Knight (using `h''`)
which can be combined into: A ∈ Knight ↔ A ∉ Knave.

Similarly for the other two levels, we can conclude A ∉ Knight ↔ A ∈ Knave

These two theorems will be very useful in the following world. They are now unlocked as the following:
```

```

------------------------

We have proven:
```
(Knight : Finset K) (Knave : Finset K)
(h : Knight ∩ Knave = ∅ )
(h' : A ∈ Knight)
  : A ∉ Knave 

(Knight : Finset K ) (Knave : Finset K)
(h : Knight ∩ Knave = ∅ )
(h' : ¬ (B ∈ Knave))
(h'' : B ∈ Knight ∨ B ∈ Knave)
  :  B ∈ Knight := by
```

"
