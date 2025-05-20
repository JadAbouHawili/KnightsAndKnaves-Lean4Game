import Game.Metadata
import Game.Levels.DSL_Knights_Knaves.L01_IamKnave
import Game.Levels.DSL_Knights_Knaves.L02_2plus2
import Game.Levels.DSL_Knights_Knaves.L03_prob26
import Game.Levels.DSL_Knights_Knaves.L04_IKnaveOrKnave
import Game.Levels.DSL_Knights_Knaves.L05_prob29
import Game.Levels.DSL_Knights_Knaves.L06_prob33
import Game.Levels.DSL_Knights_Knaves.L07_difftype
import Game.Levels.DSL_Knights_Knaves.L08_sametype
import Game.Levels.DSL_Knights_Knaves.L09_same
import Game.Levels.DSL_Knights_Knaves.L10_allofus
import Game.Levels.DSL_Knights_Knaves.L11_prob32
import Game.Levels.DSL_Knights_Knaves.L12_31
import Game.Levels.DSL_Knights_Knaves.L13_prob27
World "DSL_Knights_Knaves"
Title "DSL Knights and Knaves"
Introduction
"
We will introduce the knights and knaves puzzle here explaining rules of the game and the corresponding lean representation.

The setting is an island.
Every islander will make a statement. There are two types of islanders, 'knights' and 'knaves'.

For a given islander `A`,
- The proposition that `A` is a knight
```
A.isKnight
```
- The proposition that `A` is a knave
```
A.isKnave
```

Every islander is either a knight or a knave:
```
isKnight_or_isKnave (A : Islander)
: A.isKnight ∨ A.isKnave
```

Knights always tell the truth, and 'knaves' that always lie.

`knight_said`. Whatever `knight_said` is true.

```
-- A is a knight,
-- so whatever A said is true
knight_said
(stA : A said P)
(AKnight : A.isKnight) : P
```

`said_knight`. If what is said is true, then knight. 

```
-- A said something true,
-- so A is a knight.
said_knight
(stA : A said P)
(hP : P) : A.isKnight
```

`knave_said`. Whatever `knave_said` is false.

```
-- A is a knave,
-- so whatever A said is false
knave_said 
(stA : A said P) 
(AKnave : A.isKnave) : ¬P
```

`said_knave`. If what is said is false, then knave.

```
-- A said something that is false(i.e a lie),
-- so A is a knave
said_knave
(stA : A said P)
(hnP : ¬P) : A.isKnave
```

Since knights always tell the truth and knaves always lie, no islander can be both a knight and a knave.
```
not_isKnight_and_isKnave
(A : Islander) : ¬ (A.isKnight ∧ A.isKnave)
```

The objective is to conclude who is a knight and who is a knave, based on the statements of several islanders. This will be done using logical reasoning.
"
