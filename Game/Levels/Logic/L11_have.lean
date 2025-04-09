import Game.Metadata

World "Logic" 
Level 11

Title "" 

Introduction 
"
Coming back to `have`,

If you can prove something in one step then 
```
have theorem-name := proof
```
will do. 

For example, you can obtain a proof of `Q` in one step by 
```
hPQ hP
```
then `have hQ := hPQ hP` will add `hQ : Q` to the proof state i.e you have proven `Q` and `hQ` is the proof.
"

Statement {P Q R : Prop}
{hP : P}
{hPQ : P → Q}
{hQR : Q → R}
  : R := by
  tauto

Conclusion 
"
"
