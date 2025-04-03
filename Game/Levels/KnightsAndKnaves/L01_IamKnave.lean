import Game.Metadata_KnightsAndKnaves

World "KnightsAndKnaves"
Level 1

Title "I am a knave"

Introduction 
"
Let's solve the previously mentioned 'I am a knave' puzzle.

Suppose we have an inhabitant `A` which says:
```
A : I am a knave.
```

We repeat the representation here.

Formally, the statement 'I am a knave' is `A ∈ Knave`.

Remember that if `A` were a knight, then `A`'s statement is true. As an implication:
```
A ∈ Knight → A ∈ Knave
```

If `A`'s statement were true, then `A` is telling the truth so `A` must be a knight. As an implication:
```
A ∈ Knave → A ∈ Knight
```

The two can be combined as
```
stA : A ∈ Knight ↔ A ∈ Knave
```

Similarly, if `A` were a knave then `A`'s statement is false. As an implication:
```
A ∈ Knave → ¬(A ∈ Knave)
```

If `A`'s statement were false `A` must be a knave. As an implication:
```
¬(A ∈ Knave) → (A ∈ Knave)
```

Both can be combined as:
```
stAn : A ∈ Knave ↔ ¬(A ∈ Knave)
```

If `A` were a knight (i.e telling the truth), then `A` would be a knave which is a contradiction.

Similarly if `A`  were a knave(i.e lying) then `A` would be a knight which is a contradiction.

Regardless of what `A` is, we fall into contradiction. The proof will take all cases for `A`, which are either the fact of always telling the truth(Knight) or always lying(Knave) and will show this contradiction.

Remember that `A` is either a knight or a knave, represented by `h1` , and our reasoning was taking every case and showing that we reach the same conclusion `False` in both. This is known as a proof by cases.

For this, we need the `cases` tactic. Try `cases h1` and see what happens.
"
#check 2=2
open settheory_approach
variable [DecidableEq Inhabitant]

macro_rules
| `(tactic| contradiction) => 
  do `(tactic |solve | ( apply disjoint_without  ; repeat assumption) )
Statement IamKnave
{h1 : A ∈ Knight ∨ A ∈ Knave }
{stA : A ∈ Knight  ↔ (A ∈ Knave) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave) }
  : False := by

  {
  cases h1
  ·
   Hint
  "Notice that `h1` is now replaced by `h_1`, and we have two goals to prove instead of one. 
  The difference between each is that in the first, A is a knight(`h_1 : A ∈ Knight`) and in the second A is a knave(`h_1 : A ∈ Knave`).  

  Conclude  `AKnave : A ∈ Knave` using `stA` , `h_1`.
  "

   have AKnave := stA.mp h
   Hint
  "So now we have `h_1 : A ∈ Knight` and `{AKnave} : A ∈ Knave`. 

  But, remember that `Knight` and `Knave` are disjoint i.e have no common element , `h : Knight ∩ Knave = ∅`.
  "

   Hint (hidden := true) "Remember the `disjoint` theorem"
   #check Knight
   #check dis
   --have := dis
   --apply disjoint
   --#check disjoint_without
   --apply disjoint_without
   --repeat assumption
   contradiction
    
  -- exact dis
   --exact dis h AKnave

  ·
   Hint
   "
   Notice that h_1 is now `A ∈ Knave`.

    Conclude `A ∈ Knight` using `stA` , `h_1`.
  "
   have AKnight:= stA.mpr h
   Hint
  "So now we have `h_1 : A ∈ Knave` and `{AKnight} : A ∈ Knight`. 

  But, remember that `Knight` and `Knave` are disjoint i.e have no common element , `h : Knight ∩ Knave = ∅`.
  "
   Hint (hidden := true) "Remember the `disjoint` theorem"
   contradiction
   --exact disjoint h AKnight h_1
  }
Conclusion
"
If you have heard about the liar's paradox before (https://en.wikipedia.org/wiki/Liar_paradox), then this should look familiar.

A saying 'I am a knave' is like A saying 'I am a liar' or 'I am lying'.

In this level, we have proven the following theorem which is now available to you:
```
IamKnave (h : Knight ∩ Knave = ∅) (h1 : A ∈ Knight ∨ A ∈ Knave) (stA : A ∈ Knight ↔ A ∈ Knave) : False
```
"

NewTheorem IamKnave
NewDefinition Iff
