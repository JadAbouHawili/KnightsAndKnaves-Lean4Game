import Game.Metadata

World "KnightsAndKnavesLemmas"
Level 7

Title "If you're not a knave, then the only option left is a knight."

Introduction 
"
You are either a knight or a knave (`h`). If you are not a knave (`h'`), then the only option left is being a knight.

In other words,  

In this level, we know:
```
A ∈ Knight ∨ A ∈ Knave
A ∉ Knave
```
In our case, `P` is `A ∈ Knight`. Since we know `A ∉ Knave` then we can say that `A ∈ Knave = False`. Replacing this in the `∨` expression gives us `A ∈ Knight ∨ False`.

In other words, we have that `A ∈ Knight ∨ False` is true. So we must have `A ∈ Knight`.

"

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
"
