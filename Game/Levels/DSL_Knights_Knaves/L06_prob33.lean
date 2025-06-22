import Game.Metadata
import Game.LevelLemmas.dsl_KnightsAndKnaves

World "DSL_Knights_Knaves"
Level 6

Title ""
Introduction
"
Suppose `A` says, 'I am a knave, but `B` isn't.' 
What are `A` and `B`?

Change the goal to `¬A.isKnight`. You write `¬` by \\not.
"

set_option push_neg.use_distrib true
open Islander
Statement
{stA : A said (A.isKnave  and  ¬B.isKnave) }
: ¬A.isKnight and B.isKnave := by 
  have AnK : ¬A.isKnight
  Hint "
Assume `A` is a knight.
  "
  intro AKnight
  Hint
  "
Conclude that `A`'s statement is true.
  "
  have AKnave := knight_said stA AKnight
  Hint (strict := true)
  "
Now you have that `A` is a knave , which is a contradiction

Remeber that `{AKnave}.left : A.isKnave`.
  "
  have AKnave := AKnave.left
  contradiction

  Hint 
  "
Now that we know that `A` is not a knight, we know that what `A` said was a lie.

Use
```
notknight_said
    (stA : A said P) 
    ( notKnight : ¬isKnight A) : ¬P
```
  "
  have st := notknight_said stA AnK 
  Hint
  "
Use `not_and_or` at `{st}`
  "
  rw [not_and_or] at st
  Hint 
  "
`A` is not a knight means that `A` is a knave, so `{st}` could be simplified.

Obtain `A.isKnave` using `knight_to_knave`, and simplify `{st}` obtaining `B.isKnave`.

After that, close the goal
  "
  knight_to_knave at AnK
  simp [AnK] at st

  constructor
  knight_to_knave
  assumption
  assumption

Conclusion
"
"
NewTheorem Islander.notknight_said
