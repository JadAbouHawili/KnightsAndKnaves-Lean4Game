import Game.Metadata

World "DSL_Knights_Knaves" 
Level 1

Title "" 

Introduction 
"
"

open Islander
Statement  (hAKn : A said A.isKnave): False := by 
  knight_or_knave A with hA hnA 
  · have hnA := knight_said hAKn hA
    #check not_isKnight_and_isKnave
    apply not_isKnight_and_isKnave 
    constructor
    assumption ; assumption
  · have hnA := knave_said hAKn hnA
    contradiction

Conclusion
"
"
#check knight_said
NewTheorem Islander.knight_said
--TheoremDoc MyNat.add_zero as "add_zero" in "+"
