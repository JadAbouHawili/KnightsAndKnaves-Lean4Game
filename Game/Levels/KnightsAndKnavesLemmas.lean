import Game.Metadata
import Game.Levels.KnightsAndKnavesLemmas.L01_whydisjoint

import Game.Levels.KnightsAndKnavesLemmas.L02_inleft
import Game.Levels.KnightsAndKnavesLemmas.L03_Knight_NotKnave
import Game.Levels.KnightsAndKnavesLemmas.L04_inright
import Game.Levels.KnightsAndKnavesLemmas.L05_Knave_NotKnight
import Game.Levels.KnightsAndKnavesLemmas.L06_NotKnight_Knave
import Game.Levels.KnightsAndKnavesLemmas.L07_NotKnave_Knight

World "KnightsAndKnavesLemmas"
Title "Knights and Knaves, lemmas"
#check Set.mem_def
#check Set.instMembershipSet
#check Finset
Introduction 
"
We will introduce the knights and knaves puzzle here. In this world, you will have to prove basic but important theorems which will be used in the world after this one to solve actual knights and knaves puzzles.

The setting is an island  in which certain inhabitants called 'knights' always tell the truth, and others called 'knaves' always lie.

Every inhabitant is either a knight or a knave, there is no third option. Formally:
```
A ∈ Knight ∨ A ∈ Knave.
```

Let `Knight` be the set of inhabitants that are knights, i.e always tell the truth.
Let `Knave` be the set of inhabitants that are knaves, i.e always lies.
In a proof state, this would look like:
```
Objects
Knight Knave : Finset Inhabitant
```
`Knight` is a finite set where its elements are of type `Inhabitant` and these elements satisfy the propery of always telling the truth.
`Knave` is a finite set where its elements are of type `Inhabitant` and these elements satisfy the property of always lying.

Since knights always tell the truth and knaves always lie, no inhabitant can be both a knight and a knave. So the intersection of the two sets is empty i.e `Knight ∩ Knave = ∅`. We say the two sets `Knight`, `Knave` are disjoint.

The statement `A ∈ Knight` is read as: `A` belongs to the finite set `Knight`(`A in Knight`), and it should be understood as 'A IS Knight' i.e 'A' always tells the truth.
Similarly, the statement `A ∉ Knight` is read as: `A` doesn't belong to the finite set `Knight`(`A not in Knight`), and it should be understood as 'A ISNOT Knight'.
The same reasoning applies to `x ∈ Knave`, `x ∉ Knave`.

The objective is to conclude who is a knight and who is a knave, based on the statements of several inhabitants. This will be done using logical reasoning. Every inhabitant will make at most one statement.

get a taste:
Logic Puzzles: Knights and Knaves - YouTube
https://www.youtube.com/watch?v=jY6dvQUHIOs
"
