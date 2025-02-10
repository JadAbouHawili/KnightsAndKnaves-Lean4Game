import Game.Metadata
--import Game.Levels.KnightsAndKnavesLemmas.L01_whydisjoint
World "KnightsAndKnavesLemmas"
Level 2

Title "`inleft_notinright`"

Introduction 
"
For two disjoint sets `left`,`right`(i.e with no common element), `A ∈ left` means `A` can't be in `right` i.e `¬ (A ∈ right)` or `A ∉ right`.

The reasoning goes as follows:
Assume `A ∈ right`. This is done using `intro` tactic.
"

Statement inleft_notinright
  {left : Finset K} {right : Finset K}
{inst : DecidableEq K}
(h : left ∩ right = ∅ )
(Aleft : A ∈ left) : A ∉ right := by
  intro a
  Hint
  "
This proof state is what `disjoint` was created to deal with.
 "
  exact disjoint h Aleft a

Conclusion
"
We have proved the following theorem that you can use in future levels:
```
theorem inleft_notinright
(h : left ∩ right = ∅ )
(Aleft : A ∈ left)
: A ∉ right
```

Example:
For a goal `A ∉ right`:
`exact inleft_notinright h Aleft` will close the goal.

The theorem `inleft_notinright` can be used for any two disjoint sets. The two we are interested in of course are `Knight`,`Knave`.

In the next level, you will use this theorem to prove that if `A` is a knight (`A ∈ Knight`), then `A` is not a knave (`A ∉ Knave`).
"

NewTheorem inleft_notinright
