import Game.Metadata


World "KnightsAndKnaves2"
Level 6

Title ""

Introduction
"
`A`: `C` is a knave or `B` is a knight.

`B`: `A` is a knave, if and only if `C` is a knight.
"

--A ⇔ (¬C ∨ B)
--B ⇔ (¬A ⇔ C)
Statement {A B C : Prop}
{stA: A ↔ (¬C ∨ B)}
{stAn: ¬A ↔ (C ∧ ¬B)}
{stB: B ↔ (¬A ↔ C)}
{stBn: ¬B ↔ ¬(¬A ↔ C)}
: A ∧ B ∧ ¬C := by
    Hint (strict := true)
    "
Use `have` to set `A` as the goal
    "
    have hA : A
    Hint (strict := true)
        "
    We want to prove `A`, to do this we will prove `¬¬A`, i.e. `¬A → False`. The tactic `by_contra` facilitates this, assuming `¬A` and changing the goal to `False`.

    Assuming `hA : ¬A`:
    - Prove `hCnB : C ∧ ¬ B` using `stAn`, `nA`.
    - Prove `AsameC : ¬(¬A ↔ C)` using `stBn`, `hCnB.right : ¬B`
    - Prove `nAiffC : ¬A ↔ C` using `iff_of_true`, `nA`, `hCnB.left : C`
    - Prove `False` from `nAiffC` and `AsameC` therefore proving that `¬A → False`, i.e. `¬¬A`, i.e. `A`
    "
    by_contra nA
    have hCnB:=  (stAn.mp nA)
    have AsameC := stBn.mp hCnB.right
    have nAiffC:= iff_of_true nA hCnB.left
    contradiction

    Hint
    "
Prove `nCorB : ¬C ∨ B` using `stA`, `{hA}`
    "
    have nCorB := stA.mp hA
    Hint
    "
Take cases for `{nCorB}`.
    "
    cases nCorB
    Hint
    "
Use `iff_of_true` to prove `A ↔ ¬C`
    "
    have AiffnC := iff_of_true hA h
    Hint
    "
Use `iff_not_comm` to prove `C ↔ ¬A`
    "
    have CiffnA := iff_not_comm.mp AiffnC
    Hint
    "
Prove `B` using `stB`, `CiffnA.symm : C ↔ ¬A` (symm for 'symmetry').
    "
    have hB := stB.mpr CiffnA.symm
    Hint
    "
Given `hP : P`, `hQ : Q`, `hR : R` and the goal `P ∧ Q ∧ R`, you can close this goal using:
```
exact ⟨hP,hQ,hR⟩
```
where `⟨⟩` is typed as \\\<\\\> (this is to avoid nesting `And.intro` inside another).
    "
    exact ⟨hA,hB,h⟩

    Hint
    "
Prove `nAiffC : ¬A ↔ C` using `stB`, `h`
    "
    have nAiffC := stB.mp h
    Hint
    "
Prove `AiffnC : A ↔ ¬C` using `iff_not_comm`, `nAiffC.symm : C ↔ ¬A` (symm for 'symmetry').
    "
    have AiffnC := iff_not_comm.mp nAiffC.symm
    Hint
    "
Prove `hC : C` using `AiffnC : A ↔ ¬C`, `hA : A`
    "
    have hC := AiffnC.mp hA
    Hint
    "
Split using `constructor` or use `⟨⟩` notation.
    "
    exact ⟨hA,h,hC⟩

Conclusion
"
"
#check iff_not_comm
NewTheorem iff_not_comm
