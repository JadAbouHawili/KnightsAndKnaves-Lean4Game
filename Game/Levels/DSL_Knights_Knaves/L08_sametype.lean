import Game.Metadata

import Game.LevelLemmas.dsl_KnightsAndKnaves

World "DSL_Knights_Knaves"
Level 8

Title ""

Introduction
"
You have met a group of 2 islanders. Their names are `Robert` and `Ira`.

`Robert` says: `Ira` is my type.

`Ira` says: `Robert` is truthful.

A knight or a knave will say they are the same type as a knight. So when `Robert` says they are the same type as `Ira`, we know that `Ira` is a knight.

Let's start by proving `Ira.isKnight`
"

--https://philosophy.hku.hk/think/logic/knights.php

open Islander

example 
{Robert Ira : Islander}
{stR : Robert said (Robert.isKnight ↔ Ira.isKnight)}
: Ira.isKnight := by 
  by_contra nIKnight
  simp [nIKnight] at stR
  knight_to_knave at stR
  exact dsl_iamknave stR

Statement 
{Robert Ira : Islander}
{stR : Robert said (Robert.isKnight ↔ Ira.isKnight)}
{stI : Ira said (Robert.isKnight)}
:  Robert.isKnight and Ira.isKnight := by {
  have IKnight : Ira.isKnight 
  Hint
  "
Assume by contradiction that `¬Ira.isKnight` using the `by_contra` tactic.
  "
  by_contra nIKnight
  Hint
  "
  We will now simplify `stR`.

  Because `¬Ira.isKnight` , `Robert.isKnight ↔ Ira.isKnight ` can be simplified to `¬ Robert.isKnight`
  "
  simp [nIKnight] at stR
  Hint
  "
  `stR` now becomes `Robert said ¬ Robert.isKnight`.

  Change that to `Robert said Robert.isKnave`

  "
  knight_to_knave at stR
  Hint
  "
`Robert` is saying 'I am a knave' which is a contradiction. Use the appropriate theorem
  "
  Hint (hidden := true)
  "
`dsl_iamknave`
  "
  exact dsl_iamknave stR

  Hint
  "
Now that `Ira` is a knight, conclude that `Robert` is a knight and close the goal.
  "
  have RKnight := knight_said stI IKnight
  constructor
  assumption ; assumption

  }

example
  {Inhabitant : Type}
  {Robert Ira: Inhabitant}
  {Knight : Set Inhabitant} 
  {Knave : Set Inhabitant}
  {h : Knight ∩ Knave = ∅ }
  {Or : ∀(x :Inhabitant), x ∈ Knight ∨ x ∈ Knave}
  {stR : Robert ∈ Knight ↔ (Robert ∈ Knight ↔ Ira ∈ Knight)}
  {stI : Ira ∈ Knight ↔ Robert ∈ Knight}
   : Robert ∈ Knight ∧ Ira ∈ Knight := by
    sorry
example
  {Inhabitant : Type}
  {Robert Ira: Inhabitant}
  {Knight : Set Inhabitant} 
  {Knave : Set Inhabitant}
  {h : Knight ∩ Knave = ∅ }
  {Or : ∀(x :Inhabitant), x ∈ Knight ∨ x ∈ Knave}
  {stR : Robert ∈ Knight ↔ Ira ∈ Knight}
  {stRn : Robert ∈ Knave ↔ Ira ∈ Knight}
  {stI : Ira ∈ Knight ↔ Robert ∈ Knight}
  {stIn : Ira ∈ Knave ↔ Robert ∈ Knave} : Robert ∈ Knight ∧ Ira ∈ Knight := by 
    have IraKnight : Ira ∈ Knight := by 
      rcases Or Robert with h_1|h_1
      · exact stR.mp h_1
      · exact stRn.mp h_1
    constructor
    · exact stI.mp IraKnight
    · assumption

Conclusion 
"
"

/-
  Hint
  "
- iff_of_true
- iff_of_false 
- not_iff_not , not_iff_not.symm

You could even use `constructor` and prove every implication.
  "
  knave_to_knight at RKnave
  have IKnave := said_knave stI RKnave
  knight_to_knave at RKnave
  knight_to_knave at stR
  rw [not_iff_not] at stR
  have : Ira.isKnave ↔ Robert.isKnave := by 
    exact iff_of_true IKnave RKnave
  have RKnight := said_knight stR this 
  contradiction
-/
