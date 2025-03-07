import Game.Metadata

import Game.LevelLemmas.dsl_KnightsAndKnaves

World "DSL_Knights_Knaves"
Level 2

Title ""

Introduction
"
Change the goal to `B.isKnave`
"

variable { P Q : Prop}
open Islander
Statement {A B C : Islander} 
{hB : B said (A said A.isKnave)}
{hC : C said B.isKnave}
: B.isKnave and C.isKnight := by 
  have BKnave : B.isKnave
  knave_to_knight
  intro BKnight
  have hA := knight_said hB BKnight
  exact dsl_iamknave hA

  constructor
  assumption

  have CKnight := said_knight hC BKnave
  assumption


#check not_isKnight_and_isKnave -- Knight ∩ Knave = ∅ 
#check isKnight_or_isKnave --  A ∈ Knight ∨ A ∈ Knave

/-
I am a knave
-/
example : A said A.isKnave ↔ False := by 
  constructor
  · intro hAKn 
    knight_or_knave A with hA hnA 
    · have hnA := knight_said hAKn hA
      #check not_isKnight_and_isKnave
      apply @not_isKnight_and_isKnave A
      assumption ; assumption
    · have hnA := knave_said hAKn hnA
      contradiction
  · intro 
    contradiction

/-
  apply  notisKnave_isKnight
  intro CKnave
  have hnC := knave_said hC CKnave
  contradiction
  -/

Conclusion 
"
"
NewTheorem dsl_iamknave
