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

If `A` were a knight, then `A`'s statement is true then `A` is a knave but thats impossible. So, if `A` were a knight then we can prove `False`.

If `A` were a knave, then `A`'s statement would be false i.e `A` is not a knave but thats impossible as well. So, if `A` were a knave then we can prove `False`.

By the rules of the game, we know that `A` is either a knight or a knave. 
```
isKnight_or_isKnave 
(A : Islander) 
: A.isKnight or A.isKnave
```

We can consider every case using the `cases` tactic.

"

open Islander

Statement dsl_iamknave  (hAKn : A said A.isKnave): False := by 
  Hint (hidden := true)
  "
Try
```
cases isKnight_or_isKnave A
```
  "
  knight_or_knave A with hA hnA 
  Hint
  "
  For the previous step, you also have the option of using the custom tactic `knight_or_knave A with AKnight AKnave`. This would allow you to name the hypothesis.

  You could also just do `knight_or_knave A` without specifying any names.

  Go back and try it before proceeding

You get two cases , the first where `h : A.isKnight` and the second where `h: A.isKnave`

We are now in the first case where `h : A.isKnight`
So, we can conclude that `A`'s statement is true.
"
  Hint (hidden := true)
"
`knight_said`

`A` is a knight, so whatever `A` said is true.
"
  have hnA := knight_said hAKn hA
  Hint
  "
We know `A` is a knight and a knave. 
This is a contradiction

Recall
```
not_isKnight_and_isKnave 
(AKnight : isKnight A) 
(AKnave : isKnave A) : False
```

You can use this to prove `False`, or use `contradiction` which has been modified to handle when `A` is a knight and a knave.
  "
  contradiction

  Hint
"
We are now in the second case where `h : A.isKnave`
So, we can conclude that `A`'s statement is false.
"
  Hint (hidden := true)
"
`knave_said`

`A` is a knave, so whatever `A` said is false.
"
  have hnA := knave_said hAKn hnA
  Hint 
  "
`A` is knave and is not a knave. 
contradiction.
  "
  contradiction

Conclusion
"
We have proved the following theorem:
```
dsl_iamknave 
(hAKn : A said A.isKnave) : False
```
which is given to you to use. 

You will need it in the next level.
"

NewTheorem Islander.knight_said Islander.said_knight Islander.knave_said Islander.said_knave Islander.isKnight Islander.isKnave Islander.not_isKnight_and_isKnave dsl_iamknave
NewDefinition DSLKnightsKnaves

NewTactic knight_or_knave
