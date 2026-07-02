import Game.MathlibTheorems
import Game.LevelLemmas.Logical

World "Logic"
Level 2

Title "And, `∧`"
Introduction
"
In this level, we introduce the `∧` logical connective (read as 'and').

Given the following proofs that `x = 2` and `y = 6`,
```
h : x = 2
h' : y = 6
```
we can construct a proof that `x = 2 AND y = 6` written in Lean notation as `x = 2 ∧ y = 6`.

We construct this expression using the `And` introduction rule `And.intro` (which introduces the `∧`
symbol)
```
And.intro (hP : P)
          (hQ : Q)
: P and Q
```

`And.intro` is a function that takes two inputs: a proof of `P` and a proof of `Q` returning a proof of `P and Q`.

"

Statement (P Q : Prop) (hP : P) (hQ : Q)
  : P and Q  := by
  {
    Hint(hidden:=true)
    "
Type `exact And.intro hP hQ`
    "
    exact And.intro hP hQ
  }

Conclusion
"
You can also use the `constructor` tactic which breaks the goal into its components: proving `P` and
`Q` individually.

Click retry and try this before moving on to the next level
"

NewTheorem And.intro
NewDefinition logic_and
NewTactic constructor
