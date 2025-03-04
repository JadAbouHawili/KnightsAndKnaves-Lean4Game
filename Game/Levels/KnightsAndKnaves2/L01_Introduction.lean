import Game.Metadata

World "KnightsAndKnaves2"
Level 1

Title ""

Introduction 
"
`A`: `B` is a knight and `C` is a knight.

`B`: `C` is a knight and `A` is a knave.
"

Statement
{A B C : Prop}
{stA : A ↔ (B ∧ C)}
{stAn : ¬A ↔ ¬(B ∧ C)}
{stB : B ↔ (C ∧ ¬A)}
{stBn : ¬B ↔ ¬C ∨ A}
: ¬A ∧ ¬B ∧ ¬C := by

  Hint 
  "
Use `have` to set `¬A` as the new goal.
  "
  have hnA : ¬A
  Hint
    "
Assuming `hA : A`:
- Prove `BC : B ∧ C` from `stA` using `A`
- Prove `CnA : C ∧ ¬A` using `stB` , `BC.left : B`
- Prove `False` using `AKnight : A`,`CnA.right : ¬A`.
    "
  intro hA
  have BC := stA.mp hA
  have CnA := stB.mp BC.left
  exact CnA.right hA

  Hint 
  "
Use `have` to set `¬C` as the new goal.
  "
  have hnC : ¬C
  Hint
    "
Assuming `hC : C`:
- Prove `hB : B` using `stB`, `C ∧ ¬A`
- Prove `hA : A` using `stA` , `B ∧ C`
- Prove `False` from `hA: A`,`hnA : ¬A`
    "
  intro hC
  have hB := stB.mpr ⟨hC,hnA⟩
  have hA := stA.mpr ⟨hB,hC⟩
  contradiction

  Hint
  "
Using `¬C`, we get `¬C ∨ A` which gives `¬B` using `stBn`.
  "
  have nCorA : ¬C ∨ A
  left
  exact hnC
  have hnB := stBn.mpr nCorA
  exact ⟨hnA,hnB,hnC⟩
