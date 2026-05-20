import Game.LevelLemmas.settheory_KnightsAndKnaves

open Inhabitant

World "SetTheory_Knights_Knaves"
Level 7

Title "Intro"

Introduction
"
You stumble into `A`,`B`.

`A` says '`B` is a knight'

`B` says 'We are different types'
"

Statement
(stA : A ∈ Knight ↔ B ∈ Knight)
(stB : B ∈ Knight ↔ A ∈ Knave )
: A ∈ Knave and B ∈ Knave := by

-- instead of rewriting explain it as transitivity of ↔
  Hint
  "
  `B ∈ Knight ↔ A ∈ Knave` means the two propositions have the same truth value , in a sense they
  are 'equal'

And so in `stA : A ∈ Knight ↔ B ∈ Knight` you can replace `B ∈ Knight` with `A ∈ Knave` by rewriting
`stB` at `stA`
  "
  Hint (hidden:=true)
  "
  rw [stB] at stA
  "
  rw [stB] at stA
  Hint
  "
Now `stA` is `A` saying I am a knave.

We can derive a proof of `False` from this and store it using `have`

Then `contradiction` would do the trick
  "
  Hint (hidden:=true) (strict:=true)
  "
Remember `IamKnave`
  "
  have:= IamKnave stA
  contradiction

Conclusion
"
"
