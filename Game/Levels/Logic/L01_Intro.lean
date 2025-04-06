import Game.Metadata
import Game.LevelLemmas.Logical


World "Logic"
Level 1

Title "Intro"

Introduction
" 
This should look familiar.

If it doesn't, then replace `P` by `x=2`.

`hP` is of type `P` and `P` is of type `Prop`. So, `hP` is a proof of `P`. Our goal is to prove `P`. We already have such a proof which is `hP`, `hP` is EXACTLY what we need to prove the goal. The type of `hP` EXACTLY matches the goal.
"

Statement (P Q R : Prop) (hP: P) (hQ: Q) (hR : R)
  : P := by
  {
   Hint (hidden := true) "Type `exact hP`!"
   exact hP
  }

Conclusion
"
In the next levels, we will discuss how to construct new propositions from old ones whose meaning and truth value would depend on those old ones.
"

NewDefinition «Prop»
