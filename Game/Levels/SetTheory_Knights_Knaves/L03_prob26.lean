import Game.LevelLemmas.settheory_KnightsAndKnaves3

open Inhabitant'

World "SetTheory_Knights_Knaves"
Level 3

Title "Intro"

Introduction
"
Three of the inhabitants `A`, `B`, and `C` were standing together in a garden.

A stranger passed by and asked `A`, 'Are you a knight or a knave?' `A` answered, but rather indistinctly, so the stranger could not make out what he said.

The stranger then asked `B`, 'What did `A` say?' `B` replied, '`A` said that he is a knave.'

At this point the third man, `C`, said, 'Don't believe `B`; he is lying!'

The question is, what are `B` and `C`?

Change the goal to `B ∈ Knave` (using the `have` tactic)
"

Statement
{hB : B ∈ Knight ↔ (A ∈ Knight ↔  A ∈ Knave)}
{hC : C ∈ Knight ↔ B ∈ Knave}
: B ∈ Knave and C ∈ Knight := by
  have BKnave : B ∈ Knave
  Hint
  "
Change the goal to `B ∉ Knight`

Use the `knight_interp` tactic. This tactics lets you interpate the goal as a statement of terms
of `Knight`
  "
  knight_interp
  Hint
  "
Assume that `B` is a knight.
  "
  intro BKnight
  Hint
  "
`B` is a knight so whatever `B` said is true.
  "
  have hA := hB.mp BKnight
  Hint
  "
If an islander says 'I am a knave', we get a contradiction, i.e. `False`.
  "
  Hint (hidden:=true) "remember `IamKnave`"
  exact IamKnave hA
  Hint
  "
Now that `B` is a knave, `C`'s statement is true then `C` is a knight.

So you would have `B` is a knave and `C` is a knight closing the goal.
  "

  have CKnight := hC.mpr BKnave

  constructor
  assumption
  assumption

Conclusion
""
