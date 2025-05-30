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

open Islander

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

Conclusion 
"
"
