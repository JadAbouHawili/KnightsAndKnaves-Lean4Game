import Game.Metadata_KnightsAndKnaves

World "KnightsAndKnaves"
Level 4

Title ""

Introduction
"
From Raymond Smullyan's book called 'What is the name of this book', part 1 chapter 3 problem 33

Suppose `A` says 'I am a knave, but `B` is not' i.e `A ∈ Knave ∧ B ∉ Knave`.

Formally,
```
stA: A ∈ Knight → A ∈ Knave ∧ B ∉ Knave
stAn : A ∈ Knave ↔ ¬(A ∈ Knave ∧ B ∉ Knave)
```

For `stAn`, the statement is equivalent to:
```
stAn : A ∈ Knave ↔ A ∉ Knave ∨ B ∈ Knave
```
"
-- prob 33
--axiom Inhabitant : Type
--axiom inst : DecidableEq Inhabitant
--axiom A : Inhabitant
--axiom B : Inhabitant
Statement

(preamble := rw [not_and_or] at stAn ; simp at stAn) 
{Inhabitant : Type}
{inst : DecidableEq Inhabitant}
{A B : Inhabitant}
{Knight : Finset Inhabitant}
{Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{h2: B ∈ Knight ∨ B ∈ Knave }
{stA : A ∈ Knight  ↔ (A ∈ Knave  ∧  B ∉ Knave) }
{stAn : A ∈ Knave  ↔ ¬(A ∈ Knave  ∧  B ∉ Knave) }
  :  A ∈ Knave ∧ B ∈ Knave:= by
--{stAn : A ∈ Knave ↔ A ∉  Knave  ∨  B ∈ Knave }
  Hint (strict := true)
    "
    Prove `A ∉ Knight`.
    "
  have AnKnight : A ∉ Knight
  Hint
  "
Assume `AKnight : A ∈ Knight`:
  "
  intro AKnight
  Hint
  "
Prove `AKnBnKn : A ∈ Knave ∧ B ∉ Knave` using `AKnight`, `stA`.
  "
  have AKnBnKn  := stA.mp AKnight
  Hint 
  "
Prove `False` using `disjoint` , `AKnBnKn.left : A ∈ Knave` , `AKnight : A ∈ Knight`.
  "
  have := AKnBnKn.left
  contradiction

  Hint "Prove `AKnave : A ∈ Knave` using `notleft_right` , `{AnKnight} : A ∉ Knight`"
  have AKnave := notleft_right h1 AnKnight
  Hint "Prove `AnKnBKn : A ∉ Knave ∨ B ∈ Knave` using `{AKnave} : A ∈ Knave` ,`stAn`"
  have AnKnBKn := stAn.mp AKnave
  Hint "
  Prove `B ∈ Knave` using  `A ∉ Knave ∨ B ∈ Knave` and `{AKnave} : A ∈ Knave`. Use `simp` here.

After that, close the goal.
  "
--  have BKnave : B ∈ Knave
--  exact notleft_right AnKnBKn AKnave 

  simp [AKnave] at AnKnBKn
  exact And.intro AKnave AnKnBKn

Conclusion
"
In the next world, we present a different way to represent the knights and knaves puzzle which would affect what the solution looks like(the patterns of reasoning won't change though, only their execution).
"
