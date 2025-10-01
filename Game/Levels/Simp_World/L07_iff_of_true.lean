import Game.Metadata


World "Simp_World"
Level 7

Title "`iff_of_true`"

Introduction
"
Here, we have that `P`,`Q` are both true.

The relevant theorem,
```
iff_of_true (ha : a) (hb : b)
  : a ↔ b
```
"

Statement { P Q : Prop} (hP : P) (hQ : Q)
  : P ↔ Q := by

  {
  exact iff_of_true hP hQ
  }

Conclusion
"
"
NewTheorem iff_of_true
