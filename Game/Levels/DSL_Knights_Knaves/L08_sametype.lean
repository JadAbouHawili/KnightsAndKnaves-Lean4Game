import Game.Metadata


World "DSL_Knights_Knaves" 
Level 8

Title "" 

Introduction 
"
"

--https://philosophy.hku.hk/think/logic/knights.php
--Here is your puzzle:
--
--You have met a group of 2 islanders. Their names are Robert and Ira.
--
--    Robert says: Ira is my type.
--    Ira says: Robert is truthful.
--solution:     A knight or a knave will say they are the same type as a knight. So when Robert says they are the same type as Ira, we know that Ira is a knight.
--    All islanders will call one of their same kind a knight. So when Ira says that Robert is a knight, we know that Robert and Ira are the same type. Since Ira is a knight, then Robert is a knight.
--
--For these reasons we know there were no knaves , and the knights were Robert and Ira.
-- there's similar level to this...
Statement
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
#check iff_not_self
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
