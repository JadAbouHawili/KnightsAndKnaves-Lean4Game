import Game.MathlibTheorems
import Game.LevelLemmas.Logical

World "Logic"
Level 1

Title "Intro"

Introduction
"
This should look familiar.

If it doesn't, then mentally replace `P` by `x = 2`.

We want to prove `P`. `hP` is a proof of `P`.

`hP` is EXACTLY what we need to prove the goal. The type of `hP` EXACTLY matches the goal.
"

Statement (P Q R : Prop) (hP: P) (hQ: Q) (hR : R)
  : P := by
  {
   Hint (hidden := true) "Type `exact hP`!"
   exact hP
  }

Conclusion
"
In the upcoming levels, we will discuss how to construct new propositions from existing ones.

Here's an example in natural language.

Given the two propositions 'The sun is shining', 'It is Monday'.

You can construct 'The sun is shining and it is monday' which is a proposition as well.
It's truth value depends on the truth value of its building blocks
"

NewDefinition «Prop»
