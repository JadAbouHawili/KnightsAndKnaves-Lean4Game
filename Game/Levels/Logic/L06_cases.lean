import Game.MathlibTheorems
import Game.LevelLemmas.Logical

World "Logic"
Level 6

Title "Proof by `cases`"

Introduction
"
In this level, we will do a 'proof by cases' using the `cases` tactic.

By `h : P or Q`, we have two cases:
`P` being true or `Q` being true.

If we consider each case individually and prove some statement `R`, then we can conclude that `R`
is true.

This is the elimination principle for `∨` which you can read about
[Or.elim](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Or.elim)

To do this, start with `cases h`
"

Statement
{P Q R : Prop}
(h : P or Q)
(hPR : P → R)
(hQR : Q → R)
  : R := by

  {
  cases h
  Hint "Combine `P → R` , `P` to get `R`"
  exact hPR h_1
  Hint "Combine `Q → R` , `Q` to get `R`"
  exact hQR h_1
  }

Conclusion
"
In the next level , we will learn about logical equivalence `↔` which states two propositions have the same truth value(either both are true or both are false)
"

NewTactic cases
