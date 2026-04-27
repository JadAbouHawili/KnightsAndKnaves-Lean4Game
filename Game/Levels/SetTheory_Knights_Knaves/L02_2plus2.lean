import Game.LevelLemmas.settheory_KnightsAndKnaves

open Inhabitant

World "SetTheory_Knights_Knaves"
Level 2

Title "Intro"

Introduction
"
`A` says 'I am a knave or 2+2=5'.

`2+2=5` is false

`P or False` is `P`

Use `simp` to do these simplications for you.
"

Statement  (stA : A ∈ Knight ↔ (A ∈ Knave or (2+2=5))) : False := by{
  simp at stA
  Hint
  "
This is identical to the previous level.

  "
  Hint (hidden:=true)
  "
Use `IamKnave`.
  "
  exact IamKnave stA
}

Conclusion
""
NewTheorem IamKnave
