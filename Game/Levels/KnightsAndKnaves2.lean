import Game.Metadata
import Game.Levels.KnightsAndKnaves2.L01_Introduction
import Game.Levels.KnightsAndKnaves2.L02_
import Game.Levels.KnightsAndKnaves2.L03_
import Game.Levels.KnightsAndKnaves2.L04_iff
import Game.Levels.KnightsAndKnaves2.L05_
import Game.Levels.KnightsAndKnaves2.L06_orIff
import Game.Levels.KnightsAndKnaves2.L07_imp
World "KnightsAndKnaves2"
Title "Knights and Knaves, Second Approach"
Introduction
"
Say we have an islander `A` who could be a knight or a knave.

`A` is represented as
```
A : Prop
```
where having the proposition `A` being true means the islander `A` is a knight and having the proposition `A` being false means the islander `A` is a knave.

Now, we intrepret having a proof of `A` as `A` being a knight, and having a proof of `¬A` as `A` being a knave.

From this, every islander being a knight or a knave is represented as follows:
```
A or ¬A
```

Knights always tell the truth, so if `A` makes some statement `P` we have that `A` being a knight implies that the statement `P` is true
```
A → P
```
Moreover, the statement `P` being true means that `A` is telling the truth i.e is a knight
```
P → A
```
which can be combined as
```
A ↔ P
```

Similarly for `A` being a knave which implies that the statement `P` is false
```
¬A → ¬P
```
Moreover, the statement `P` being false means that `A` is lying i.e is a knave
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

This representation captures the rules of the knights and knaves puzzle which are:
- Every islander is either a knight or a knave
- No islander is both a knight and a knave at the same time
- Knights always tell the truth, knaves always lie.

All puzzles in this world were generated(and possibly modified) from [wolfram cloud demonstration](https://www.wolframcloud.com/objects/demonstrations/KnightsAndKnavesPuzzleGenerator-source.nb)

Note that you could also take a more explicit truth table approach, where you list all the cases in a truth table and eliminate the cases which contradict the rules of the game(e.g `A` being a knight but `A`'s statement being false). If you are left with one possibility then the puzzle has a unique solution, otherwise it has multiple solutions.
This can be done in [prolog](https://www.youtube.com/watch?v=oEAa2pQKqQU) and [other provers](https://summerofgodel.blogspot.com/2019/04/part-6-propositional-logic-approach-to.html)
"
