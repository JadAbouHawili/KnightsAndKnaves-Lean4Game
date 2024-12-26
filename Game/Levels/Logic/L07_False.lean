import Game.Metadata

World "Logic"
Level 7

Title "From `False`, anything follows."

Introduction
"
We proved `False`, what does this mean? What can we conclude? What does `False` IMPLY?

Let's check the `→` truth table:
$$
\\begin{array}{|c|c|c|} 
\\hline
P & Q & P → Q \\\\
\\hline
T & T & T \\\\
\\hline
T & F & F \\\\
\\hline
F & T & T \\\\
\\hline
F & F & T \\\\
\\hline
\\end{array}
$$

Let's focus on part of the truth table where `P` is `False`, because we want to see what `False` implies.
$$
\\begin{array}{|c|c|c|} 
\\hline
Q & False → Q \\\\
\\hline
T & T \\\\
\\hline
F & T \\\\
\\hline
\\end{array}
$$

We have that the implication `False → Q` is true regardless what `Q` represents and regardless whether `Q` is true or is false. 
So `False` implies any proposition. This principle is known as: 'From `False` anything follows'.

Use this implication to prove `Q` where `Q` is any proposition.
"

Statement {Q : Prop} (h : False → Q) (hF : False) : Q := by 
  exact h hF

Conclusion
"
Having proven `False`, instead of going through this to prove `Q` you can use the the `contradiction` tactic. If you were able to prove `False`, then the `contradiction` tactic will prove the goal regardless what the goal is because 'from `False`, anything follows'.

Proving `False` is what's usually called deriving a contradiction, and note that to prove `False` you would first need to have a proof `P`, and a proof of `¬P` i.e `P → False`.
"

NewTactic contradiction
NewDefinition False Not
