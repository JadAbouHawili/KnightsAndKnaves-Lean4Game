import Game.LevelLemmas.dsl_KnightsAndKnaves


World "DSL_Knights_Knaves"
Level 13

Title ""

Introduction
"
Suppose the stranger, instead of asking `A` what he is,
asked `A`, 'How many knights are among you?'

Again `A` answers indistinctly. So the stranger asks `B`, 'What did `A` say?

`B` replies, '`A` said that there is one knight among us.

Then `C` says, 'Don't believe `B`; he is lying!'

Now what are `B` and `C`?
"

open Islander

Statement
(stB : B said (A said @oneisknight A B C))
(stC : C said B.isKnave)
: B.isKnave and C.isKnight := by

  Hint (strict := true)
  "
  First prove `B.isKnave`
  "
  have : B.isKnave
  Hint
  "
As usual, `knight_interp`
  "
  knight_interp
  Hint
  "
Assume `B` is a knight.
  "
  intro BKnight
  Hint
  "
  Conclude `B`'s statement
  "
  have stA := knight_said stB BKnight
  Hint
  "
We know that `{BKnight} : B.isKnight` which is `¬B.isKnave` which means `C` told a lie which means `C` is a knave.
  "
  knave_interp at BKnight
  have CKnave := said_knave stC BKnight

  Hint
  "
Take cases for `A`.
  "
  knight_or_knave A with AKnight AKnave
  Hint
  "
Conclude `A`'s statement
  "
  have hF := knight_said stA AKnight
  Hint
  "
We now know that there is only one knight but we also know that `A` is a knight and `B` is a knight. This is the contradiction needed to close the goal.

Start by `unfold oneisknight at {hF}` and using `simp`
  "
  unfold oneisknight at hF
  simp [CKnave,AKnight,BKnight] at hF
  knight_interp at hF
  simp [AKnight] at hF

  Hint
  "
Now this is the second case where `A` is a knave.

Conclude that `A`'s statement is false
  "
  have notoneknight := knave_said stA AKnave
  Hint
  "
It is not true that there is one knight, but that is the case so contradiction

`unfold oneisknight at {notoneknight}` and use `simp`
  "
  unfold oneisknight at notoneknight
  simp [BKnight,AKnave,CKnave] at notoneknight
  knight_interp at BKnight
  contradiction

  have CKnight := said_knight stC this
  constructor
  assumption
  assumption

Conclusion
"
"
