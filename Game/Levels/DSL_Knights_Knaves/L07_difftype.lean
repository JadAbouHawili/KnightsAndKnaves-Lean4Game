import Game.MathlibTheorems
import Game.LevelLemmas.dsl_KnightsAndKnaves

World "DSL_Knights_Knaves"
Level 7

Title "We are different types"

Introduction
"
You stumble into `A`,`B`.

`A` says '`B` is a knight'

`B` says 'We are different types'
"

open Islander
Statement
(stA : A said B.isKnight)
(stB : B said A.isKnave )
: A.isKnave and B.isKnave := by
  Hint
  "
Let's start by proving `A.isKnave`
  "
  have AKnave : A.isKnave
  Hint
  "
Change this to a goal about knights,
and assume `A.isKnight`
  "
  knight_interp
  intro AKnight
  Hint
  "
So, `B.isKnight` by `A`'s statement
  "
  have BKnight := knight_said stA AKnight
  Hint
  "
So `A`,`B` are the same type, but `B` being a knight also tells us that they are not.
`contradiction` (`contradiction` fails here , so use `not_isKnight_and_isKnave` here)

Conclude `¬(A.isKnight ↔ B.isKnight)` from `B`'statement then prove that `A.isKnight ↔ B.isKnight` using `iff_of_true`
  "
  have notsame := knight_said stB BKnight
  exact not_isKnight_and_isKnave AKnight notsame

  Hint
  "
Now that `A` is a knave, we can conclude `A` was lying and `B` is in fact a `knave`.

Then, close the goal.
  "
  have BKnave := knave_said stA AKnave
  knave_interp at BKnave
  constructor
  assumption
  assumption

Conclusion
"
"
