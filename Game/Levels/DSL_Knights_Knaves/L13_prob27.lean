import Game.Metadata_KnightsAndKnaves
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
Now what are B and C? 
"

-- prob 27
--open settheory_approach
--variable [DecidableEq Inhabitant]
/-
Suppose the stranger, instead of asking A what he is, 
asked A, "How many knights are among you?" Again A 
answers indistinctly. So the stranger asks B, "What did A 
say? B replies, "A said that there is one knight among us." 
Then C says, "Don't believe B; he is lying!" 
Now what are B and C? 
-/
--def oneKnight {A B C : Inhabitant} : Prop:=   (A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knight)

open Islander
Statement
{A B C : Islander}
(stB : B.isKnight ↔ (A.isKnight ↔ @oneisknight A B C))
(stC : C.isKnight ↔ B.isKnave)
: B.isKnave and C.isKnight := by

  Hint (strict := true)
  "
  First prove `B.isKnave`
  "
  have : B.isKnave 
  Hint
  "
As usual, from `knave_to_knight`
  "
  knave_to_knight
  Hint
  "
Assume `B` is a knight.
  "
  intro BKnight
  Hint
  "
You can simplify `stC` using `{BKnight}`. Change `{BKnight}` it to an expression involving knaves.
  "
  knight_to_knave at BKnight
  simp [BKnight] at stC

  Hint
  "
Take cases for A.
  "
  knight_or_knave A with AKnight AKnave
  Hint
  "
Conclude `B`'s statement
  "
  knave_to_knight at BKnight
  have oneKst := stB.mp BKnight
  Hint
  "
Conclude that there is only one knight
  "
  have oneK := oneKst.mp AKnight
  Hint
  "
Unfold that statement.

As you can see, it is not true that there only one knight and simplifying this expression will give the contradiction needed to close the goal.
  "
  unfold oneisknight at oneK
  simp [AKnight, stC, BKnight] at oneK
  knave_to_knight at oneK 
  simp [ stC, BKnight] at oneK
  contradiction

  knave_to_knight at AKnave
  Hint
  "
Again conclude B's statement
  "
  knave_to_knight at BKnight
  have onest := stB.mp BKnight
  Hint
  "
Conclude `oneisknight` using simp and what you know about `A`. 
  "
  simp [AKnave] at onest
  Hint
  "
Unfold `oneisknight` and notice that it is false, and a simplification will give the contradiction you desire.
  "
  unfold oneisknight at onest
  simp [AKnave, stC, BKnight] at onest
  knave_to_knight at onest
  simp [AKnave] at onest
  contradiction

  Hint
  "
Now we finally have that `B` is a knave. Obtain information about `C` and close the goal.
  "
  have CKnight := stC.mpr this
  constructor
  repeat assumption

Conclusion
"
"
