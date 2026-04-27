import Game.LevelLemmas.settheory_KnightsAndKnaves3

World "SetTheory_Knights_Knaves"
Level 9

Title ""

open Inhabitant'

-- prob 34, problem 34
Introduction
"
We have three inhabitants, `A`, `B`, and `C`.

Two people are said to be of the same type if they are both knights or both knaves.

`A` and `B` make the following statements:

`A`: `B` is a knave.

`B`: `A` and `C` are of the same type.
"

set_option push_neg.use_distrib true
Statement
{stA : A ∈ Knight ↔ B ∈ Knave}
{stB : B ∈ Knight ↔ (A ∈ Knight ↔ C ∈ Knight)}
(h : A ∈ Knight ∨ A ∈ Knave)
: C ∈ Knave := by

  Hint --(strict := true)
  "
Take cases for `A`
  "
  Hint (hidden:=true)(strict := true)
  "
Remember the `knight_or_knave` tactic.
  "
  rcases h with AKnight| AKnave
--  knight_or_knave A with AKnight AKnave
  Hint
  "
We are in the case where `A.isKnight`

Conclude that `B.isKnave`
  "
  have BKnave := stA.mp AKnight

  Hint
  "
Therefore, from `B`'s statement, conclude that `A` and `C` are not the same, i.e. are different.
  "
  knave_interp at stB
  have diff := stB.mp BKnave
  simp at diff

  Hint
  "
Use `not_iff`
  "
  rw [not_iff] at diff
  Hint
  "
Conclude `¬C.isKnight` and close the goal.
  "
  knight_interp at diff
  have CKnave := diff.mp AKnight
  knave_interp at CKnave
  assumption

  Hint
  "
Now that `A` is a knave.
We can conclude `B` is a knight.

which means that `A` and `C` have the same type, obtaining that `C` is a knave and closing the goal.
  "
  knave_interp at stA
  have BKnight := stA.mp AKnave
  knight_interp at BKnight
  have same := stB.mp BKnight
  knave_interp at same
  exact same.mp AKnave

Conclusion
"
"
