import Game.Metadata


World "Simp_World"
Level 9

Title "`not_iff_not`"

Introduction 
"
If we know that `¬P`,`¬Q` have the same truth value then `P`,`Q` have the same truth value.

The relevant theorem,
```
not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
```
"

Statement (h : ¬P ↔ ¬Q)
  : P ↔ Q := by

  {
  exact not_iff_not.mp h
  }

Conclusion
"
"

NewTheorem not_iff_not
