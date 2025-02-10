import Game.Metadata

#check iff_iff_implies_and_implies
--  -- (p → q ∧ ¬p → ¬q)  ↔ (p ↔ q)
#check iff_iff_and_or_not_and_not
  #check iff_and_self
  #check iff_self_and
  #check iff_iff_not_or_and_or_not
  #check IffToIf

World "KnightsAndKnaves"
Level 2

Title ""

Introduction
"
From Raymond Smullyan's book called 'What is the name of this book', part 1 chapter 3 problem 26

Three of the inhabitants `A`, `B`, and `C` were standing together in a garden.

A stranger passed by and asked `A`, 'Are you a knight or a knave?'. `A` answered, but rather indistinctly, so the stranger could not make out what he said.

The stranger then asked `B`, 'What did `A` say?'.
`B` replied, '`A` said that he is a knave.' 

At this point the third man, `C`, said, 'Don't believe `B`; he is lying!'

The question is, what are `B` and `C`?

First of all, lets simplify the statements. C's statement can be simplified to 'B is a knave.'

The statements are:
```
B says that A said 'I am a knave'
C says that B is a knave
```

The formalization is given in the proof state.

Note that for the statement of `B`, if `B` where telling the truth then `A` indeed made such a statement which is the statement 'I am a Knave' and the formalization of that is `A ∈ Knight ↔ A ∈ Knave`. So we get `stB : B ∈ Knight ↔ (A ∈ Knight ↔ A ∈ Knave)`
"
-- prob 26

Statement
  {inst : DecidableEq K}
  (Knight : Finset K ) (Knave : Finset K)
(h : Knight ∩ Knave = ∅ )
(h1 : A ∈ Knight ∨ A ∈ Knave ) 
(h2: B ∈ Knight ∨ B ∈ Knave )
(stB : B ∈ Knight ↔ ( A ∈ Knight ↔ A ∈ Knave  ) )
(stBn : B ∈ Knave ↔ ¬( A ∈ Knight ↔ A ∈ Knave  ) )
(stC : C ∈ Knight ↔ B ∈ Knave)
 : B ∈ Knave ∧ C ∈ Knight := by{
  -- much neater solution, very short and nice. book solution
  Hint "

We know that `A` saying 'I am a knave' leads to contradiction.

In implication form, `IamKnave` is of the following form:
```
(Knight ∩ Knave = ∅) →
(A ∈ Knight ∨ A ∈ Knave) →
(A ∈ Knight ↔ A ∈ Knave) → False
```

So, `IamKnave h h1` is of the following type:
```
(A ∈ Knight ↔ A ∈ Knave) → False
```
which is 
```
¬(A ∈ Knight ↔ A ∈ Knave)
```

Store this in an object using `have`, you don't have to specify the type.
  "
  have this := IamKnave h h1

  Hint
  "
  Conclude `B ∈ Knave` using `stBn` and `{this}`.
  "
  have BKnave := stBn.mpr this
  Hint
  "
  Conclude `C ∈ Knight` using `stC` and `{BKnave}`.
  "
  have CKnight := stC.mpr BKnave
  Hint
  "
  Conclude `B ∈ Knave ∧ C ∈ Knight` from `{BKnave} : B ∈ Knave`, `{CKnight} : C ∈ Knight` and use exact to close the goal.
  "
  exact And.intro BKnave CKnight
}


open Islander
#check not_isKnight_and_isKnave -- Knight ∩ Knave = ∅ 
#check isKnight_or_isKnave --  A ∈ Knight ∨ A ∈ Knave  

/-
I am a knave
-/
--open Islander
example : A said A.isKnave ↔ False := by 
  constructor
  · intro hAKn 
    knight_or_knave A with hA hnA 
    · have hnA := knight_said hAKn hA
      #check not_isKnight_and_isKnave
      apply @not_isKnight_and_isKnave A
      constructor
      assumption ; assumption
    · have hnA := knave_said hAKn hnA
      contradiction
  · intro 
    contradiction

theorem dsl_iamknave (hAKn : A said A.isKnave): False := by 
  knight_or_knave A with hA hnA 
  · have hnA := knight_said hAKn hA
    #check not_isKnight_and_isKnave
    apply @not_isKnight_and_isKnave A
    constructor
    assumption ; assumption
  · have hnA := knave_said hAKn hnA
    contradiction
example {A B C : Islander} 
{hB : B said (A said A.isKnave)}
{hC : C said B.isKnave}
: B.isKnave and C.isKnight := by 
  have BKnave : B.isKnave
  -- need to introduce apply in this game
  apply notisKnight_isKnave
  intro BKnight
  have hA := knight_said hB BKnight
  exact dsl_iamknave hA

  constructor
  assumption

  have CKnight := said_knight hC BKnave
  assumption
/-
  apply  notisKnave_isKnight
  intro CKnave 
  have hnC := knave_said hC CKnave
  contradiction
  -/

#check iff_false
#check and_imp

Conclusion
"
"
