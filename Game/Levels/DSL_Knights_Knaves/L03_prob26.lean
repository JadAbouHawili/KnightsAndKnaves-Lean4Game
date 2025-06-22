import Game.Metadata

import Game.LevelLemmas.dsl_KnightsAndKnaves

World "DSL_Knights_Knaves"
Level 3

Title ""

Introduction
"
Three of the inhabitants `A`, `B`, and `C` were standing together in a garden. 

A stranger passed by and asked `A`, 'Are you a knight or a knave?' `A` answered, but rather indistinctly, so the stranger could not make out what he said. 

The stranger then asked `B`, 'What did `A` say?' `B` replied, '`A` said that he is a knave.' 

At this point the third man, `C`, said, 'Don't believe `B`; he is lying!' 

The question is, what are `B` and `C`?

Change the goal to `B.isKnave`(using the `have` tactic)
"

variable { P Q : Prop}
open Islander
Statement 
{hB : B said (A said A.isKnave)}
{hC : C said B.isKnave}
: B.isKnave and C.isKnight := by
  have BKnave : B.isKnave
  Hint
  "
Change the goal to `¬isKnight B`

Use the `knave_to_knight` tactic.
  "
  knave_to_knight
  Hint
  "
Assume that `B` is a knight.
  "
  intro BKnight
  Hint
  "
`B` is a knight so whatever `B` said is true.
  "
  have hA := knight_said hB BKnight
  Hint
  "
If an islander says 'I am a knave', we get a contradiction i.e `False`.
  "
  exact dsl_iamknave hA
  Hint
  "
Now that `B` is a knave, `C`'s statement is true then `C` is a knight.

So you would have `B` is a knave and`C` is a knight closing the goal.
  "

  have CKnight := said_knight hC BKnave

  constructor
  assumption
  assumption

Conclusion
"
"

NewTactic knave_to_knight
