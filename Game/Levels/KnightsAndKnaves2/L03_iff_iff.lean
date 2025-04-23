import Game.Metadata


World "KnightsAndKnaves2" 
Level 3

Title "" 

Introduction
"
`Robert` says: `Ira` is my type.

`Ira` says: `Robert` is truthful.

`Ira` is my type is translated as 
```
( (Ira and Robert) or (¬Ira and ¬Robert) )
```
Notice that this is equivalent to `Ira ↔ Robert`

Replace this expression in `stR` by `Ira ↔ Robert` using
```
iff_iff_and_or_not_and_not.symm
: (a and b or ¬a and ¬b ) ↔ (a ↔ b)
```

then use `stI` to prove `Robert` and obtain `Ira`.
"

#check iff_iff_and_or_not_and_not

Statement 
{Robert Ira : Prop}
{stR : Robert ↔ ( (Ira and Robert) or (¬Ira and ¬Robert) )}
{stI : Ira ↔ Robert}
: Robert ∧ Ira := by 
  Hint (hidden := true)
  "
Remember the interpretation where you can treat `↔` like `=`(refer to `↔` docs for an example).
  "
  rw [iff_iff_and_or_not_and_not.symm] at stR
  have R := stR.mpr stI
  have I := stI.mpr R
  constructor
  repeat assumption

example 
{Robert Ira : Prop}
{stR : Robert ↔ (Ira ↔ Robert)}
{stI : Ira ↔ Robert}
: Robert ∧ Ira := by 
  have : Robert 
  Hint
  "
Assume `¬Robert` and prove `False`.

`by_contra nRobert` does that.
  "
  by_contra h
  Hint 
  "
`Robert` is equivalent to `Ira ↔ Robert`

So `¬Robert` is equivalent to `¬(Ira ↔ Robert)` contradicting `stI`.
  "
  rw [stR] at h
  contradiction

  Hint 
  "
Now that you know `Robert`, conclude `Ira`
  "
  have := stI.mpr this
  constructor
  repeat assumption

Conclusion 
"
"
