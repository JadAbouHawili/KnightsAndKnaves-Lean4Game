import Game.Metadata


World "Simp_World"
Level 6

Title "`iff_of_false`"

Introduction
"
`P ↔ Q` means that `P`,`Q` have the same truth value.

If both of them are true, we can conclude `P ↔ Q`.

If both of them are false, we can conclude `P ↔ Q` as well.

Here, we have that `P`,`Q` are both false.

The relevant theorem,
```
iff_of_false (ha : ¬a) (hb : ¬b)
  : a ↔ b
```
"

Statement {P Q : Prop} (hnP : ¬P) (hnQ : ¬Q)
  : P ↔ Q := by

  {
  exact iff_of_false hnP hnQ
  }

Conclusion
"
"
NewTheorem iff_of_false
