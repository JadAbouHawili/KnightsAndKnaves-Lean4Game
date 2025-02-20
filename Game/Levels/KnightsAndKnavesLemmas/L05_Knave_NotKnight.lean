import Game.Metadata

import Game.LevelLemmas.settheory
import Game.LevelLemmas.KnightsAndKnaves
World "KnightsAndKnavesLemmas"
Level 5

Title "A Knave is not a knight."

Introduction 
"
If you are a knave, then you are definitely not a knight. Recall that knights always tell the truth and knaves always lie.

This is implied by the assumption:
```
h : Knight ∩ Knave = ∅ 
```

Note that this level is identical to the previous one except the fact that the set `left` is now called `Knight` and the set `right` is now called `Knave`.

This doesn't change anything of course, what changes are the names you and Lean would be seeing. If everything is renamed consistently, nothing changes.

You can use the theorem proved in the previous level `inright_notinleft` giving it the necessary arguments.
"

Statement 
  {inst : DecidableEq K}
  {Knight : Finset K} {Knave : Finset K}
(h : Knight ∩ Knave = ∅ )
(h' : A ∈ Knave)
  : ¬ (A ∈ Knight) := by
  {
    exact inright_notinleft h h'
  }

Conclusion 
"
"
