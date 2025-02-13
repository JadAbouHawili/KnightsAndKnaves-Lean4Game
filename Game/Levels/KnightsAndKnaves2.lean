import Game.Metadata
import Game.Levels.KnightsAndKnaves2.L01_Introduction
import Game.Levels.KnightsAndKnaves2.L02_iff
import Game.Levels.KnightsAndKnaves2.L03_
import Game.Levels.KnightsAndKnaves2.L04_orIff
import Game.Levels.KnightsAndKnaves2.L05_imp
World "KnightsAndKnaves2"
Title "Knights and Knaves, Second Approach"
Introduction
"
Say we have an islander `A` who could be a knight or a knave.
`A` is represented as
```
A : Prop
```
a proposition where having the proposition `A` being true means the islander `A` is a knight and having the proposition `A` being false means the islander `A` is a knave. 

From this, every islander being a knight or a knave is represented as follows:
```
A or ¬A
```

Knights always tell the truth, so if `A` makes some statement `P` we have that `A` being a knight implies that statement `P` is true
```
A → P
```
and that the statement `P` being true means th at `A` is telling the truth i.e is a knight
```
P → A
```
which are combined as 
```
A ↔ P
```

Similarly for `A` being a knave which implies that the statement `P` is false
```
¬A → ¬P
```
and that the statement `P` being false means that `A` is lying i.e is a knave
```
¬P → ¬A
```
which are combined as 
```
¬A ↔ ¬P
```

No islander can be a knight and a knave at the same time because
```
A ∧ ¬A
```
is false.

-----------
In this world, we also deal with the knights and knaves puzzle with the difference being the representation of the problems in Lean and therefore the solution to the puzzles as well.

The setup is as follows:
We exploit the binary nature of an inhabitant. There are two options and no third, either a knight or a knave. So, we declare an object of type `Prop` for every inhabitant. 

Say we had three inhabitants `A,B,C` , we would declare the following propositions:
```
variable {A B C : Prop}
```
Now, we intrepret having a proof of `A` as `A` being a knight, and having a proof of `¬A` as `A` being a knave.

We have the following correspondence:
$
\\begin{array}{|c|c|c|} 
\\hline
\\text{Old way} & \\text{New way} \\\\
\\hline
h : A ∈ Knight & h : A \\\\
\\hline
h : A ∉ Knight & h : ¬A \\\\
\\hline
h : A ∈ Knave  & h : ¬A \\\\
\\hline
h : A ∉ Knave  & h : ¬¬A \\\\
\\hline
\\end{array}
$

The translation of statements made by each inhabitant into a propositional formula remains the same, using `↔` but of course instead of `A ∈ Knight` we just have `A` and instead of `A ∈ Knave` we just have `¬A`.

Notice that there are no explicit assumptions in this representation, but that doesn't mean that this representation is less faithful.

We know that any proposition is either true or false, in our context this would translate to every inhabitant is either a knight or a knave. 
```
A ∈ Knight ∨ A ∈ Knave 
```
translates to
```
A ∨ ¬A
```

Moreoever, we know that `A ∧ ¬A` is false, which would translate to the fact that no inhabitant can be both a knight or a knave.
```
A ∈ Knight ∧ A ∈ Knave
```
which within the previous representation of finite sets would mean that the set knight and the set knave are disjoint.
```
Knight ∩ Knave = ∅
```

Correspondence:
$
\\begin{array}{|c|c|c|} 
\\hline
\\text{Old way} & \\text{New way} \\\\
\\hline
h : A ∈ Knight ∨ A ∈ Knave & h : A ∨ ¬A \\\\
\\hline
h : Knight ∩ Knave = ∅ & h: A ∧ ¬A  \\\\
\\hline
\\end{array}
$

All puzzles were generated(and possibly modified) from https://www.wolframcloud.com/objects/demonstrations/KnightsAndKnavesPuzzleGenerator-source.nb.
"
