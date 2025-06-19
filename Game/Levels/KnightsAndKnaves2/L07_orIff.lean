import Game.Metadata

World "KnightsAndKnaves2"
Level 7

Title ""

Introduction 
"
`A`: `B` is a knight or `C` is a knight.
`B`: `C` is a knave, if and only if `A` is a knave
"
--A ⇔ (B ∨ C)
--B ⇔ (¬C ⇔ ¬A)

Statement {A B C : Prop}
{stA : A ↔ (B ∨ C)}
{stAn : ¬A ↔ ¬(B ∨ C)}
{stB : B ↔ (¬C ↔ ¬A)}
{stBn : ¬B ↔ ¬(¬C ↔ ¬A)}
: A ∧ B ∧ C := by
  Hint (strict := true)
    "
Use `have` to set `B` as the goal
    "
  have hB : B
  Hint (strict :=true)
  "
Assuming `nB : ¬B`:
- Prove `CdiffA : ¬(¬C ↔ ¬A)` using `stBn`, `nB`
- Using `simp` and `nB : ¬B`, reduce `stA` to `stA : A ↔ C`. (`B ∨ C`, `C` have the same truth value (for `C` being true or false) when `B` is false.
- Using `not_iff_not`, reduce `¬C ↔ ¬A` in `CdiffA` to `C ↔ A`.
- Prove `False` using `CdiffA`, `stA.symm : A ↔ C`
  "
  by_contra nB
  have CdiffA := stBn.mp nB
  --#check notleft_right
  simp [nB] at stA
  rw [not_iff_not] at CdiffA
  exact CdiffA stA.symm

  Hint
  "
Prove `CsameA : C ↔ A` using `stB`, `{hB}`
  "
  have CsameA := stB.mp hB
  Hint
  "
Prove `BorC : B ∨ C` using `{hB}`
  "
  have BorC : B ∨ C := by left ; assumption 
  Hint
  "
Prove `hA : A` using `stA`, `{BorC}`.
  "
  have hA := stA.mpr BorC
  Hint
  "
Rewrite `CsameA` to `CsameA : C ↔ A` using `not_iff_not`
  "
  rw [not_iff_not] at CsameA
  Hint
  "
Prove `hC : C` using `{CsameA}`, `{hA}`
  "
  have hC := CsameA.mpr hA
  Hint
  "
Use constructor
  "
  constructor
  assumption
  constructor
  assumption
  assumption

Conclusion
"
"
