import Game.Metadata
import Game.Levels.DSL_Knights_Knaves.L01_IamKnave
import Game.Levels.DSL_Knights_Knaves.L02_prob26
import Game.Levels.DSL_Knights_Knaves.L03_IKnaveOrKnave
import Game.Levels.DSL_Knights_Knaves.L04_prob33
World "DSL_Knights_Knaves"
Title "DSL"
Introduction 
"
We will introduce the knights and knaves puzzle here.

The setting is an island. 
Every islander will make a statement. There are two types of islanders, 'knights' that always tell the truth, and 'knaves' that always lie.
This is represented by the following rules:
```
-- The proposition that the islander A is a knight
A.isKnight 

-- The proposition that the islander A is a knave
A.isKnave 

isKnight_or_isKnave (A : Islander) : A.isKnight ∨ A.isKnave

knight_said : (A said P) → A.isKnight → P
said_knight : (A said P) →  P → A.isKnight 
knave_said  : (A said P) →  A.isKnave → ¬P
said_knave  : (A said P) →  ¬P → A.isKnave
```

In a proof state, this would look like:
```
Objects
Knight Knave : Finset Inhabitant
```

Since knights always tell the truth and knaves always lie, no islander can be both a knight and a knave. This is represented as:
```
not_isKnight_and_isKnave (A : Islander) : ¬ (A.isKnight ∧ A.isKnave)
```

The objective is to conclude who is a knight and who is a knave, based on the statements of several inhabitants. This will be done using logical reasoning.
"
