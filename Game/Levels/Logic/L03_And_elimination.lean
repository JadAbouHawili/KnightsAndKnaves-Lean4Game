import Game.MathlibTheorems
import Game.LevelLemmas.Logical

World "Logic"
Level 3

Title "`∧` Elimination Rule "
Introduction
"
In the previous level , we defined the `∧` introduction rule.

In this level, we will define the `∧` elimination rule.

An introduction rule 'introduces' a symbol , in this case proving a statement of `and`.

An elimination rule 'eliminates' a symbol extracting information from it. For an expression `P and Q`
, applying the elimination rule would give you a proof of `P` and a proof of `Q` separately.

To extract the left side of `and` , use the left elimination rule
```
And.left (self : a and b) : a
```

To extract the right side of `and` , use the right elimination rule
```
And.right (self : a and b) : b
```

Which side do we need to prove the goal?
"

Statement (P Q : Prop) (hP : P and Q)
  : P  := by
  {
    Hint(hidden:=true)
    "
The left side. `And.left hP`
    "
    exact hP.left
  }

Conclusion
"
`hP.left` is a shorthand equivalent to `And.left hP`

Click retry and solve this level using `hP.left`
"

NewTheorem And.left And.right
NewDefinition logic_and
