import Game.Metadata
import Game.LevelLemmas.dsl_KnightsAndKnaves
#check dsl_iamknave
World "DSL_Knights_Knaves" 
Level 3

Title "" 

Introduction 
"
`A` says 'I am a knave or `B` is a knave'.
"

open Islander
Statement 
{A B : Islander}
{stA : A said (A.isKnave or B.isKnave)}
: A.isKnight and B.isKnave := by 
  Hint 
  "
Let's start with proving that `A` is a knight. (use `have`)
  "
  have AKnight : A.isKnight 
  Hint
  "
Having 
```
h : P → Q

Goal: 
Q
```
then `apply h` will change the goal from `Q` to `P` , because proving `P` would give you `Q`.

Here, we have
```
notisKnave_isKnight : ¬isKnave A → isKnight A 
```

We want to prove `isKnight A`, and a way to get there is through proving `¬isKnave A`.
  "
  knight_to_knave
  --apply notisKnave_isKnight
  Hint "
  For the previous step and to avoid having you going through the hoops everytime , you can simply execute the custom tactic `knight_to_knave` which works as its name suggests.
  Go back and try it before proceeding

Assume `isKnave A`
  "
  intro AKnave

  Hint
  "
Let's first prove `isKnave A or isKnave B`.

  "
  --apply said_knight at stA
  have orexp: isKnave A or isKnave B
  Hint
  "
Choose which side to prove, `left` or `right`?
  "
  left
  assumption
  Hint
  "
For,
```
h : P → Q
hP : P
```

`apply h at hP` would change `hP : P ` to `hP : Q`.

This is giving the implication the argument it needs to reach the conclusion.

We can prove `isKnave A or isKnave B` , which means that A is telling the truth.

But we know `A` is a knave, which gives us `False`.
  "
  #check said_knight
  have AKnight := said_knight stA orexp
  contradiction

  constructor
  assumption
  Hint "
`A` is a knight, so we can conclude `A`'s statement.
  "
  have orexp := knight_said stA AKnight
  Hint 
  "
`orexp` can be simplified, using the fact that `A` is a knight and that knights are not knaves.
  "
  apply notleft_right at orexp 
  --exact orexp (isKnight_notisKnave AKnight)
  apply orexp
  intro 
  contradiction

  --simp [AKnight,isKnight_notisKnave] at orexp
  --assumption

Conclusion 
"
"
NewTactic knight_to_knave
