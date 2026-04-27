import Game.LevelLemmas.settheory_KnightsAndKnaves

open Inhabitant

World "SetTheory_Knights_Knaves"
Level 7

Title "Intro"

Introduction
"
You stumble into `A`,`B`.

`A` says '`B` is a knight'

`B` says 'We are different types'
"

Statement
(stA : A ∈ Knight↔ B ∈ Knight)
(stAn : A ∈ Knave ↔ B ∉ Knight)
(stB : B ∈ Knight ↔ ( ¬ (A ∈ Knight ↔ B ∈ Knight) ) )
: A ∈ Knave and B ∈ Knave := by
  Hint
  "
Let's start by proving `A.isKnave`
  "
  have AKnave : A ∈ Knave
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
  have BKnight := stA.mp AKnight
  Hint
  "
So `A`,`B` are the same type, but `B` being a knight also tells us that they are not. contradiction

Conclude `¬(A.isKnight ↔ B.isKnight)` from `B`'statement then prove that `A.isKnight ↔ B.isKnight` using `iff_of_true`
  "
  have notsame := stB.mp BKnight
  exact notsame (iff_of_true AKnight BKnight)

  Hint
  "
Now that `A` is a knave, we can conclude `A` was lying and `B` is in fact a `knave`.

Then, close the goal.
  "
  have BKnave := stAn.mp AKnave
  knave_interp at BKnave
  constructor
  assumption
  assumption

Conclusion
"
"
