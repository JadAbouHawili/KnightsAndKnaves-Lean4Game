import Game.LevelLemmas.settheory_KnightsAndKnaves

open Inhabitant

World "SetTheory_Knights_Knaves"
Level 8

Title "Intro"

Introduction
"
You have met a group of 2 islanders. Their names are `Robert` and `Ira`.

`Robert` says: `Ira` is my type.

`Ira` says: `Robert` is truthful.

A knight or a knave will say they are the same type as a knight. So when `Robert` says they are the same type as `Ira`, we know that `Ira` is a knight.

Let's start by proving `Ira ∈ Knight`
"

theorem iff_assoc {P Q R: Prop}
: ((P ↔ Q) ↔ R) ↔ (P ↔ (Q ↔ R)) := by{
  grind
}

Statement
{Robert Ira : Inhabitant}
{stR : Robert ∈ Knight ↔ (Robert ∈ Knight ↔ Ira ∈ Knight)}
{stI : Ira ∈ Knight ↔ (Robert ∈ Knight)}
:  Robert ∈ Knight and Ira ∈ Knight := by {
  have iKnight : Ira ∈ Knight
  Hint
  "
Assume by contradiction(`by_contra`)  that `Ira ∉ Knight`
  "
  by_contra
  Hint
  "
We can now conclude that `Robert ∉ Knight` using `stI`
  "
  Hint (hidden:=true) "Remember `simp`"
  simp [this] at stI
  Hint
  "
`Robert` and `Ira` have the same type which means that `Robert ∈ Knight` by `stR`

But we know that `Robert ∉ Knight`.
  "
  simp [stI,this] at stR

  have := stI.mp iKnight
  constructor ; assumption ; assumption
}

Conclusion
"
"
