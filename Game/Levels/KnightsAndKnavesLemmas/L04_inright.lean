import Game.Metadata

import Game.LevelLemmas.settheory
import Game.LevelLemmas.KnightsAndKnaves
World "KnightsAndKnavesLemmas" 
Level 4

Title "`inright_notinleft`"

Introduction
"
The reasoning goes as follows:

Assume `A ∈ left`. This is done using `intro` tactic.
"

Statement inright_notinleft
  {left : Finset K} {right : Finset K}
{inst : DecidableEq K}
(h : left ∩ right = ∅ )
(Aright : A ∈ right) : A ∉ left := by
  intro a 
  Hint "Look familiar? This is exactly like the previous level which gave us `disjoint` theorem."
  exact disjoint h a Aright

----
  --rw [Finset.inter_comm] at h
  --exact inleft_notinright h h' 

Conclusion 
"
We have proved the following theorem that you can use in future levels:
```
theorem inright_notinleft
(h : left ∩ right = ∅ )
(Aright : A ∈ right)
: A ∉ left
```

Example:
For a goal `A ∉ left`:
`exact inright_notinleft h Aright` will close the goal.

The theorem `inright_notinleft` can be used for any two disjoint sets. The two we are interested in of course are `Knight`,`Knave`.

In the next level, you will use this theorem to prove that if `A` is a knave (`A ∈ Knave`), then `A` is not a knight (`A ∉ Knight`).
"
NewTheorem inright_notinleft
