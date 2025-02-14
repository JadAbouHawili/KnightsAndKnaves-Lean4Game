import Game.Metadata

World "Logic"
Level 6

Title "Proving an implication, Implication as the goal" 

Introduction 
"
The goal, translated to english is: 'If P is true, then P is true'.

To prove such a goal, we need to assume that `P` is true. Then, we have to prove that `P` is true.

To do this, we need to assume the premise i.e introduce it to our assumptions. We can do this using `intro`.

After that , we have to prove the consequent.
"

Statement {P :Prop}
  : P → P  := by
  {
    intro hP
    exact hP
  }

Conclusion 
"
use `intro name` to give the introduced hypothesis a name
"
NewTactic intro
