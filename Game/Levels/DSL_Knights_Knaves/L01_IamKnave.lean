import Game.Metadata

import Game.LevelLemmas.dsl_KnightsAndKnaves
World "DSL_Knights_Knaves"
Level 1

Title "I am a knave, I am a liar"

Introduction
"
In this level, we present the 'I am a knave' puzzle.

The given islander `A` says 'I am a knave'
```
Asaid : A said A.isKnave
```

The goal is to prove `False`, i.e that given the rules of the game , if `A` says 'I am a knave' we have a contradiction.

By the rules of the game, we know that `A` is either a knight or a knave. 
```
isKnight_or_isKnave 
(A : Islander) : A.isKnight or A.isKnave
```

Try
```
cases isKnight_or_isKnave A
```
"

open Islander

Statement  (hAKn : A said A.isKnave): False := by 
  knight_or_knave A with hA hnA 
  Hint
  "
  For the previous step and to avoid having you going through the hoops everytime , you can simply execute the custom tactic `knight_or_knave A with AKnight AKnave`.
  Go back and try it before proceeding

You get two cases , the first where `h : A.isKnight` and the second where `h: A.isKnave`

We are now in the first case where `h : A.isKnight`
"
  have hnA := knight_said hAKn hA
  #check not_isKnight_and_isKnave
  contradiction

  have hnA := knave_said hAKn hnA
  contradiction

Conclusion
"
"

NewTheorem Islander.knight_said Islander.said_knight Islander.knave_said Islander.said_knave Islander.isKnight Islander.isKnave
NewDefinition DSLKnightsKnaves 

NewTactic knight_or_knave
