import Game.Metadata

World "KnightsAndKnaves"
Level 3

Title ""

Introduction
"
`A` says 'I am a knave or `B` is a knave'.

Formally,
```
stA : A ∈ Knave ↔ ¬ (A ∈ Knave ∨ B ∈ Knave)
```

We have `¬(P ∨ Q)` when `P` is false and `Q` is false, i.e `¬P ∧ ¬Q`.
Therefore, we represent `stA` as the following:
```
stA : A ∈ Knave ↔ A ∉ Knave ∧ B ∉ Knave
```
"

Statement 
{inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ }
{h1 :  A ∈ Knight ∨ A ∈ Knave}
{h2 :  B ∈ Knight ∨ B ∈ Knave}
{stA : A ∈ Knight ↔ (A ∈ Knave ∨ B ∈ Knave) }
{stAn : A ∈ Knave ↔ (A ∉ Knave ∧ B ∉ Knave) }
: A ∈ Knight ∧ B ∈ Knave := by

  Hint (strict := true)
  "
First prove `A ∉ Knave`, which takes multiple steps.
  "
  have AnKnave : A ∉ Knave
  Hint
    "
Assume `AKnave : A ∈ Knave`
    "
  intro AKnave
  Hint
  "
- Prove `ABnotKnave : A ∉ Knave ∧ B ∉ Knave` using `stAn`,`AKnave`. (one step proof)
  "
  have ABKnave := stAn.mp AKnave 
  Hint
  "
Prove `False` using `ABnotKnave.left : A ∉ Knave` , `AKnave : A ∈ Knave`
  "
  exact ABKnave.left AKnave

  Hint
  "
Prove `AKnight : A ∈ Knight` using `{AnKnave} : A ∉ Knave` , `notright_left`. (one step proof)
  "
  have AKnight := notright_left h1  AnKnave

  Hint
  "
Prove `AorBKn: A ∈ Knave ∨ B ∈ Knave` using `{AKnight}`, `stA`. (one step proof)
  "
  have AorBKn := stA.mp AKnight
  Hint
  "
Prove `BKnave : B ∈ Knave` using `{AorBKn}` , `{AnKnave}`. (`have`, one step proof)
  "
  have BKnave := notleft_right AorBKn AnKnave
  Hint
  "
Prove the goal using `AKnight` , `BKnave`.
  "
  exact And.intro AKnight BKnave



Conclusion
"
"

NewTheorem not_or
