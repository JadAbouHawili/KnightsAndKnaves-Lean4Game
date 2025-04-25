import Game.Metadata

import Game.LevelLemmas.dsl_KnightsAndKnaves

World "DSL_Knights_Knaves" 
Level 9

Title "" 

Introduction 
"
You have met a group of 2 islanders. Their names are Robert and Ira.

Robert says: Ira is my type.
Ira says: Robert is truthful.


"

--https://philosophy.hku.hk/think/logic/knights.php
--Here is your puzzle:
--
--solution:     A knight or a knave will say they are the same type as a knight. So when Robert says they are the same type as Ira, we know that Ira is a knight.
--    All islanders will call one of their same kind a knight. So when Ira says that Robert is a knight, we know that Robert and Ira are the same type. Since Ira is a knight, then Robert is a knight.
--
--For these reasons we know there were no knaves , and the knights were Robert and Ira.
-- there's similar level to this...
open Islander
Statement 
{stR : Robert said (Robert.isKnight ↔ Ira.isKnight)}
{stI : Ira said (Robert.isKnight)}
:  Robert.isKnight and Ira.isKnight := by 
  Hint 
  "
Start by proving `¬Robert.isKnave`
  "
  have RKnight: ¬Robert.isKnave   
  Hint
  "
Assume `R.isKnave`
  "
  intro RKnave 
  Hint
  "
So `Robert` is not a knight, so `Ira` was lying .

Therefore `Ira` is a knave
  "
  knave_to_knight at RKnave
  have IKnave := said_knave stI RKnave
  Hint 
  "
`Robert` are `Ira` are the same, but we know they are not by `Robert`'s lie.
This is a contradiction.

First, conclude that `Robert`'s statement is false i.e `¬(Robert.isKnight ↔ Ira.isKnight)` then prove `Robert.isKnight ↔ Ira.isKnight`
  "
  knave_to_knight at IKnave 
  have same : Robert.isKnight ↔ Ira.isKnight 
  exact iff_of_false RKnave IKnave 

  have RKnight := said_knight stR same
  contradiction

  Hint
  "
Now that `Robert` is a knight, then `Ira` and `Robert` have the same type, and therefore `Ira` is a knight.

Conclude `Robert`'s statement then use that to get `Ira.isKnight`.

Close the goal.
  "
  knave_to_knight at RKnight 
  have same := knight_said stR RKnight
  constructor
  assumption
  rw [same.symm]
  assumption

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
