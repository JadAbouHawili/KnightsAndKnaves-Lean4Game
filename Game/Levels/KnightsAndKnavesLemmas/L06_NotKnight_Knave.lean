import Game.Metadata

import Game.LevelLemmas.settheory
import Game.LevelLemmas.KnightsAndKnaves
World "KnightsAndKnavesLemmas"
Level 6

Title "If you're not a knight, then the only option left is a knave."

Introduction 
"
You are either a knight or a knave. If you are not a knight, then the only option left is being a knave.

In this level, we know:
```
A ∈ Knight ∨ A ∈ Knave
A ∉ Knight
```
and want to prove:
```
A ∈ Knave
```

In other words, we know that the left side of `∨` is not true and we want to prove the right side. This is a job for `notleft_right`.
"

/-

In our case, `P` is `A ∈ Knave`. Since we know `A ∉ Knight` then we can say that `A ∈ Knight = False`. Replacing this in the `∨` expression gives us `False ∨ A ∈ Knave`.

So we must have `A ∈ Knave`.
-/

Statement
  {inst : DecidableEq K}
  {Knight : Finset K} {Knave : Finset K}
{h : Knight ∩ Knave = ∅ }
{Or : A ∈ Knight ∨ A ∈ Knave}
(h' : ¬ (A ∈ Knight) )
: A ∈ Knave  := by

  {
    exact notleft_right Or h'
  }

#check iff_iff_implies_and_implies
Conclusion 
""

NewTactic exfalso
