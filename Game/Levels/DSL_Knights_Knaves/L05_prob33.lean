import Game.Metadata
import Game.LevelLemmas.dsl_KnightsAndKnaves

World "DSL_Knights_Knaves"
Level 5

Title ""
Introduction
"
Suppose A says, 'I am a knave, but B isn't.' 
What are A and B?

Change the goal to `¬A.isKnight`
"

set_option push_neg.use_distrib true
open Islander
Statement
{A B : Islander}
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
  Hint "
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
  /-
obtain that `isKnave A` and then use `knave_said`.
  -/
  have st := notknight_said stA AnK 
  Hint
  "
`h: ¬( P and Q)` means that both `P`,`Q` are not true at the same time which means one of them has to be false i.e `h : ¬P or ¬Q`.

You can apply this using
```
push_neg at h
```
which 'pushes' the 'negation' inside and applying the appropriate rules.
  "
  push_neg at st
  Hint 
  "
`A` is not a knight means that `A` is a knave, so `{st}` could be simplified.

Obtain `A.isKnave`, and simplify `{st}` obtaining `B.isKnave`.

After that, close the goal
  "
  simp [AnK,notisKnight_isKnave] at st

  constructor
  assumption
  assumption

Conclusion
"
"
NewTactic push_neg
NewTheorem Islander.notknight_said
