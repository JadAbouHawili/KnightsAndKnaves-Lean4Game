import Game.MathlibTheorems
import Game.LevelLemmas.Logical

World "Logic"
Level 7

Title "Proof by `cases`"

Introduction
"
To eliminate an `∨` hypothesis, what we can do is take cases. We assume the left case and prove
the goal `R`, then we assume the right case and prove the goal `R`. Thus, we now know that `R` is
true.

In other words, a 'proof by cases' using the `cases` tactic.

To do this, start with `cases h`


By `h : P or Q`, we have two cases:
`P` being true or `Q` being true.

If we consider each case individually and prove some statement `R`, then we can conclude that `R`
is true.

[Or.elim](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Or.elim) is the
elimination principle for `∨`.
"

Statement
{P Q R : Prop}
(h : P or Q)
(hPR : P → R)
(hQR : Q → R)
  : R := by

  {
  cases h
  Hint (strict := true) "Combine `P → R` , `P` to get `R`"
  exact hPR h_1
  Hint (strict := true) "Combine `Q → R` , `Q` to get `R`"
  exact hQR h_1
  }

Conclusion
"
In the next level , we will learn about logical equivalence `↔` which states that two propositions
have the same truth value either both being true or both being false
"

NewTactic cases
