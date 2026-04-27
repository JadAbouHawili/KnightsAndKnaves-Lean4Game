import Game.LevelLemmas.settheory_KnightsAndKnaves

open Inhabitant

World "SetTheory_Knights_Knaves"
Level 1

Title "Intro"

Introduction
"
A : I am a Knave

We want to prove that this is a contradiction , an inhabitant of the island can never assert that they are a knave(i.e a liar)

We know that either `A ∈ Knight` or `A ∈ Knave`. Let's handle each case.

Use the tactic `knight_or_knave A with h1 h2`. `h1` would be the first case `A ∈ Knight` , `h2` would be the second case`A ∈ Knave`.
(You can choose any name for `h1` , `h2`)
"

Statement
(stA : A ∈ Knight ↔ (A ∈ Knave) )
  : False := by
  {
    knight_or_knave A with AKnight AKnave
    Hint
    "
    Prove that `A ∈ Knave`
    "
    have := stA.mp AKnight
    Hint
    "
    `A` is a knight and a knave. This is a `contradiction`
    "
    contradiction
    Hint
    "
    Prove that `A ∈ Knight`
    "
    have := stA.mpr AKnave
    Hint
    "
    `A` is a knight and a knave. This is a `contradiction`
    "
    contradiction
  }

Conclusion
""

NewTactic knight_or_knave
