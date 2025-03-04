import Game.Metadata
import Game.Levels.DSL_Knights_Knaves.L01_IamKnave
import Game.Levels.DSL_Knights_Knaves.L02_prob26
import Game.Levels.DSL_Knights_Knaves.L03_IKnaveOrKnave
import Game.Levels.DSL_Knights_Knaves.L04_prob33
World "DSL_Knights_Knaves"
Title "DSL Knights and Knaves"
Introduction
"
We will introduce the knights and knaves puzzle here explaining rules of the game and the corresponding lean representation.

The setting is an island.
Every islander will make a statement. There are two types of islanders, 'knights' and knaves.
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
isKnight_or_isKnave (A : Islander) : A.isKnight ∨ A.isKnave
```

Knights always tell the truth, and 'knaves' that always lie.
```
-- A is a knight, so whatever A said is true
knight_said : (A said P) → A.isKnight → P
-- A said something true, so A is a knight.
said_knight : (A said P) →  P → A.isKnight

-- A is a knave, so whatever A said is false
knave_said  : (A said P) →  A.isKnave → ¬P
-- A said something that is false(i.e a lie), so A is a knave
said_knave  : (A said P) →  ¬P → A.isKnave
```

`P → Q → R` means if `P` is true then the implication `Q → R` is true, but if you knew `Q` as well then you can get `R`.

As an example,
```
h : P → Q → R
hP : P
hQ : Q
``` 
`h` takes two arguments and gives `R`.

Given the first argument, we get
```
h hP : Q → R
```
and giving the second,
```
h hP hQ : R
```

Since knights always tell the truth and knaves always lie, no islander can be both a knight and a knave.
```
not_isKnight_and_isKnave (A : Islander) : ¬ (A.isKnight ∧ A.isKnave)
```

The objective is to conclude who is a knight and who is a knave, based on the statements of several inhabitants. This will be done using logical reasoning.
"
