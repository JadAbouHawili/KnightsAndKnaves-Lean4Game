import Game.Metadata
import Game.LevelLemmas.dsl_KnightsAndKnaves

World "DSL_Knights_Knaves"
Level 10

Title "allKnights or allKnaves"

Introduction
"
A says B is a knight
B says all of us are knights
C says A  is a knight or B is a knight

Notice in the proof state,
```
allKnights
allKnaves
```

You can `unfold` to get
```
A.isKnight ∧ B.isKnight ∧ C.isKnave 
```
by
```
unfold allKnights at stB
```
(similarly for `allKnaves`)

However, this will make the proof state look cluttered so don't `unfold`.
"

/-
-/
open Islander

#check allKnights
#check allKnaves
Statement
{stA : A said B.isKnight}
{stB : B said (@allKnights A B C)}
{stC : C said A.isKnight or B.isKnight}
: (@allKnights A B C)  ∨ (@allKnaves A B C):= by 
  Hint (strict := true)
  "
First, take cases for `B`.
  "
  knight_or_knave B
  Hint
  "
We are at the cases where `B.isKnight`
Conclude that `B`'s statement is true
  "
  have all := knight_said stB h
  Hint
  "
`left` or `right` part of the goal?
  "
  left
  assumption

  Hint
  "
Now we have that `B.isKnave`.
Get `¬B.isKnight`
  "
  knave_to_knight at h
  Hint
  "
So, `A`'s statement is false.

Conclude that `A` is a knave.
  "
  have AKnave := said_knave stA h
  Hint
  "
Now we have that `A.isKnave`
Get `¬A.isKnight`
  "
  knave_to_knight at AKnave
  Hint
  "
  Now, `C`'s statement is false , so conclude that `C` is a knave.

  You can do this in a number of ways:
  - Use `have` to construct a proof that `¬ (A.isKnight or B.isKnight)`
  - Use `simp` on `stC`, to obtain `C said False`. Conclude `C` is a knave using `said_knave`, `not_false : ¬False`.

  - etc...

  Once you have `C.isKnave` then everyone is a knave.(`right` side of the goal)

  You can `unfold` the goal if that facilitates your reasoning.
  "
  simp [h,AKnave] at stC
  have CKnave := said_knave stC (not_false)
  right
  unfold allKnaves
  knave_to_knight at *
  simp [h,AKnave,CKnave]

Conclusion
"
"
