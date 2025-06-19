import Game.Metadata
import Game.LevelLemmas.dsl_KnightsAndKnaves


World "DSL_Knights_Knaves"
Level 11

Title "allKnaves, exactlyOneIsKnave"

Introduction
"
`A`: All of us are knaves.

`B`: Exactly one of us is a knave.
"

-- prob 32
open Islander
Statement
{A B C : Islander}
{stA : A said @allKnaves A B C}
{stB : B said @exactlyOneIsKnave A B C}
: A.isKnave and C.isKnight
:= by
  Hint (strict := true)
  "
Start by proving `¬A.isKnight`
  "
  have AKnave : ¬A.isKnight
  Hint
  "
Assume `A` is a knight, and conclude that everyone must be a knave.
  "
  intro AKnight
  have allKnave := knight_said stA AKnight
  Hint
  "
This would mean that `A` is also a knave, which is absurd.

You can `unfold allKnaves at {allKnave}` and extract `A.isKnave` from that.
  "
  Hint (hidden := true)
  "
`{allKnave}.left` will do it.
  "
  unfold allKnaves at allKnave
  have := allKnave.left
  contradiction

  Hint 
  "
Now that `A` is not a knight, conclude that not everyone is a knave.
  "
  have notallKnave:= notknight_said stA AKnave
  Hint
  "
Take cases for `B`
  "
  knight_or_knave B with BKnight BKnave 
  Hint
  "
Knowing that `B` is a knight, conclude that there is exactly one knave.
  "
  have exactlyoneKnave := knight_said stB BKnight
  Hint
  "
Notice what we have at our disposal.

We have `A` is a knave, `B` is a knight, and that there is exactly one knave. So `C` must be a knight.

You can obtain `C` by using the fact that `A` is a knave, `B` is a knight and simplifying the expression `{exactlyoneKnave}`.

`unfold exactlyOneIsKnave at {exactlyoneKnave}` first then use `simp`.

If it doesn't get simplified enough, then change the hypothesis involved from `knight_to_knave` or vice versa 
  "
  unfold exactlyOneIsKnave at exactlyoneKnave
  simp [AKnave, BKnight] at exactlyoneKnave
  assumption 

  Hint
  "
Now we are in the case where `B` is a knave.

Notice what we have.

We have that `A` is a knave, `B` is a knave, and that not everyone is a knave. 

So `C` must be a knight.

Solving this is in the same spirit of what you previously did.

`unfold allKnaves` then simplify it using the fact that `A,B` are knaves
  "
  unfold allKnaves at notallKnave 
  knight_to_knave at AKnave
  simp [AKnave,BKnave] at notallKnave
  constructor
  assumption
  knight_to_knave
  assumption

Conclusion
"
"
NewDefinition exactlyOneIsKnave
