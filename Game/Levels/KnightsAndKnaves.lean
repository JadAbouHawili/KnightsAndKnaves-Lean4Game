import Game.Levels.KnightsAndKnaves.L01_IamKnave
import Game.Levels.KnightsAndKnaves.L02_prob26
import Game.Levels.KnightsAndKnaves.L03_IKnaveOrKnave
import Game.Levels.KnightsAndKnaves.L04_prob33
World "KnightsAndKnaves"
Title "Knights And Knaves"

Introduction 
"
Suppose the island has an inhabitant `A` which says the following statement,
```
A says 'I am a knave'
```

Formally, the statement 'I am a knave' is `A ∈ Knave`.

Remember that if `A` were a knight, then `A`'s statement is true. As an implication:
```
A ∈ Knight → A ∈ Knave
```

If `A`'s statement were true, then `A` is telling the truth so `A` must be a knight. As an implication:
```
A ∈ Knave → A ∈ Knight
```

The two can be combined as 
```
stA : A ∈ Knight ↔ A ∈ Knave
```

Similarly, if `A` were a knave then `A`'s statement is false. As an implication:
```
A ∈ Knave → ¬(A ∈ Knave)
```

If `A`'s statement were false `A` must be a knave. As an implication:
```
¬(A ∈ Knave) → (A ∈ Knave)
```

Both can be combined as:
```
stAn : A ∈ Knave ↔ ¬(A ∈ Knave)
```
"
