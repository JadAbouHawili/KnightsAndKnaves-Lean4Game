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
  apply notisKnave_isKnight
  Hint "
Assume `isKnave A`
  "
  intro AKnave

  Hint
  "
For,
```
h : P → Q
hP : P
```

`apply h at hP` would change `hP : P ` to `hP : Q`. 

We can prove `isKnave A or isKnave B` , which means that A is telling the truth. 

But we know `A` is a knave, which gives us `False`.
  "
  --apply said_knight at stA
  have orexp: isKnave A or isKnave B
  left 
  assumption
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
