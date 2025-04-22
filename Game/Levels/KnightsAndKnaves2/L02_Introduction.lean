import Game.Metadata

World "KnightsAndKnaves2"
Level 2

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

Each can be done in one step, so the appropriate `have` syntax should be used.
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

For proving `hB : B` , you would need to pass a proof of `C ∧ ¬A` to `stB.mpr`. The `\\<\\>` notation is appropriate here.(although you could just use `And.intro`)
    "
  intro hC
  have hB := stB.mpr ⟨hC,hnA⟩
  have hA := stA.mpr ⟨hB,hC⟩
  contradiction

  Hint
  "
Using `¬C`, we get `¬C ∨ A` which gives `¬B` using `stBn`.

After which, you need to close the goal of the form 
```
_ and _ and _
```

The goal is implicitly
```
¬A and (¬B and ¬C)
```

You can use
```
And.intro (_) (And.intro _ _)
```
replacing `_` with the appropriate terms.

Moreover,
you could also use the ⟨⟩ notation,
```
⟨_,_,_⟩
```
replacing the `_` with the appropriate terms.

You could even use `have` to first prove `¬B and ¬C` and add it to the hypothesis,then prove the goal.
  "
  have nCorA : ¬C ∨ A
  left
  exact hnC
  have hnB := stBn.mpr nCorA
  exact ⟨hnA,hnB,hnC⟩
