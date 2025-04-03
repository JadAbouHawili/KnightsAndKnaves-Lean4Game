import Game.Metadata

import Game.LevelLemmas.dsl_KnightsAndKnaves

World "DSL_Knights_Knaves"
Level 10

Title ""

-- prob 34 , problem 34
Introduction
"
We have three inhabitants, `A`, `B`, and `C`.

Two people are said to be of the same type if they are both knights or both knaves. 

`A` and `B` make the following statements:
`A`: `B` is a knave.
`B`: `A` and `C` are of the same type.
"

theorem not_iff' {P Q : Prop}
 : ¬(P ↔ Q) ↔ (P ↔ ¬Q) := by 
  --#check Iff.symm
  --#check symm
  #check Iff.symm
  #check not_iff_comm
  #check not_iff_not
  nth_rw  2 [(@not_not P).symm]
  rw [not_iff_not]
  exact Classical.not_iff

open Islander
Statement
{A B C : Islander}
{stA : A said B.isKnave}
{stB : B said (A.isKnight ↔ C.isKnight)}
: C.isKnave := by
  Hint
  "
Take cases for `A`
  "
  knight_or_knave A with AKnight AKnave
  Hint
  "
We are in the cases where `A.isKnight`

Conclude that `B.isKnave`
  "
  have BKnave := knight_said stA AKnight

  Hint
  "
Therefore, from `B`'s statement conclude that `A` and `C` are not the same i.e are different.
  "
  have diff : ¬(A.isKnight ↔ C.isKnight)
  intro same
  have BKnight := said_knight stB same
  contradiction


  #check not_iff
  Hint
  "
Use `not_iff'`
  "
  rw [not_iff'] at diff
  Hint 
  "
Conclude `¬C.isKnight` and close the goal.
  "
  have CKnave := diff.mp AKnight
  knight_to_knave at CKnave
  assumption

  Hint 
  "
Now that `A` is a knave. 
We can conlude `B` is a knight.

which means that `A` and `C` have the same type, obtaining the `C` is a knave and closing the goal.
  "
  have BKnight := knave_said stA AKnave 
  knave_to_knight at BKnight
  have same := knight_said stB BKnight
  knight_to_knave at same
  rw [not_iff_not] at same
  exact same.mp AKnave

Conclusion
"
"
NewTheorem not_iff'
