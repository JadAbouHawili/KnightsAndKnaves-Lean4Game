import Game.Metadata

variable (P Q R : Prop)

Introduction 
"
# Two ways of dealing with ∧ in the goal
In Lean, to prove `P ∧ Q`, you need a proof of `P` and a proof of `Q`.

## first way
Giving these two proofs to the And introduction rule will construct a proof of `P ∧ Q`. Here's the type of `And.intro`:
```
  And.intro  (left : P) (right : Q) : P ∧ Q
```
where `P Q : Prop`

## second way
Using the `constructor` tactic will split a goal of the form `P ∧ Q` into two subgoals `P`,`Q` where you can deal with eac one separetly
"

example (hP : P) (hQ : Q)
  : P ∧ Q  := by

  {
    Hint (hidden:=true) "Try `exact And.intro hP hQ` or `constructor`" 
    Branch
       exact And.intro hP hQ 
    constructor
    Hint "Notice that the goal is now `P`"
    exact hP
    Hint "After closing the goal `P`, you now have to close the goal `Q`"
    exact hQ
  }
