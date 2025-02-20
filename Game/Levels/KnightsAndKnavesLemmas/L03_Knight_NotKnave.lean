import Game.Metadata

import Game.LevelLemmas.settheory
import Game.LevelLemmas.KnightsAndKnaves
World "KnightsAndKnavesLemmas"
Level 3

Title "A Knight is not a knave."

Introduction 
"
If you are a knight, then you are definitely not a knave. Recall that knights always tell the truth and knaves always lie.

This is implied by the assumption:
```
h : Knight ∩ Knave = ∅ 
```

Note that this level is identical to the previous one except the fact that the set `left` is now called `Knight` and the set `right` is now called `Knave`.

This doesn't change anything of course, what changes are the names you and Lean would be seeing. If everything is renamed consistently, nothing changes.

You can use the theorem proved in the previous level `inleft_notinright` giving it the necessary arguments.
"

Statement
  {A : Inhabitant}
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ } (AKnight : A ∈ Knight)
  : A ∉ Knave := by
  {
    exact inleft_notinright h AKnight
  }

Conclusion 
"
"
--NewTactic by_contra

