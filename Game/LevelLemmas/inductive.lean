import Game.Metadata
inductive Person (A : Type)
| knight : Person A
| knave : Person A
| normal : Person A
--| dontknow : Person 
open Person 
--def A  := knight
--def B := Person
--def C := Person
--variable {A B C : Person}
#check Or

/-
inductive Or (a b : Prop) : Prop where
  /-- `Or.inl` is "left injection" into an `Or`. If `h : a` then `Or.inl h : a ∨ b`. -/
  | inl (h : a) : Or a b
  /-- `Or.inr` is "right injection" into an `Or`. If `h : b` then `Or.inr h : a ∨ b`. -/
  | inr (h : b) : Or a b
  -/
inductive Islander2 (A : Prop) : Prop where
  /-- `Or.inl` is "left injection" into an `Or`. If `h : a` then `Or.inl h : a ∨ b`. -/
  | knight (h : A) : Islander2 A
  /-- `Or.inr` is "right injection" into an `Or`. If `h : b` then `Or.inr h : a ∨ b`. -/
  | knave (h : ¬A) : Islander2 A
  

#check em
macro "prop_cases" t1:term : tactic => 
do`(tactic| cases em $t1)

--macro_rules
--  | `(cases $r:term) => `(cases em $r)

--macro "cases" t1:term : tactic => 
--do`(tactic| cases em $t1)
--macro_rules
--| `(tactic| cases t1:term) => 
--  do `(tactic|  cases em t1)

  --|first | ( apply not_isKnight_and_isKnave ; constructor ; assumption ; assumption   ) )

--macro_rules
--| `(tactic| cases t1:Lean.Parser.Tactic.casesTarget) => 
--  do `(cases em t1 )
example {B : Prop} {H : B ∨ ¬B} {h : Islander2 B}  : 2=2 := by 

  -- modify cases tactic so that when given a prop ...
  --prop_cases B
  --cases h
  prop_cases B
  sorry
  --sorry
  sorry

inductive Person2 (A : Prop) where
  /-- `Or.inl` is "left injection" into an `Or`. If `h : a` then `Or.inl h : a ∨ b`. -/
  | knight (h : A) : (Person2 A)
  /-- `Or.inr` is "right injection" into an `Or`. If `h : b` then `Or.inr h : a ∨ b`. -/
  | knave (h : ¬A) : Person2 A

--theorem Or.intro_left (b : Prop) (h : a) : Or a b :=
--  Or.inl h
--
--/-- Alias for `Or.inr`. -/
--theorem Or.intro_right (a : Prop) (h : b) : Or a b :=
--  Or.inr h
/-
example
{P Q : Prop} { A : Prop} (H : P ∨ Q) : 2=2 := by 
  cases H
  cases (Person2)
/-
disadvantages of using inductive types,  

-/
def isKnight : Person → Prop | knight => true | knave => false | normal => false 
def isKnave : Person → Prop | knight => false | knave => true | normal => false 
def isNormal : Person → Prop | knight  => false | knave  => false | normal  => true 

    
-- evalutes to whether stA true or not
-- any person here not just A
def statementA : Person → Prop | p  => match p with | knight => isNormal knight | knave =>(isNormal knave) | normal => true 
--def statementAmod := (isKnight A) →  (isNormal A)
def statmentB: Person  → Prop | p => match p with | knight => statementA knight | knave => ¬ (statementA knave)|normal => false -- here we don't know, B being normal we don't know if A's st is true or false|--normal => statementA normal
def statmentC: Person  → Prop | p => match p with | knight => ¬ (isNormal knight ) | knave => ¬ (isNormal knave) | normal => true

-- not clear from statementA what the actual statement of A is...
example  (A B C : Person) (hA : A = knight) (hB : B = knight)  : 2=2 := by 
  #check statementA 
  --#print statementA

  have stAatA:= statementA 
  -- can't see the statement
  -- not self contained, not easy to reuse
  -- would have to make a whole list of definitions to the user which would be very annoying, the user wont memorize what everything means and will refer to that list constantly, normally the user would just look at the proof state and know
  unfold statementA at stAatA
  have stAatB:= statementA B
   
  rfl 
example (A : Person ) ( h : A = normal): isNormal A := 
  by 
  rw [h]
  unfold isNormal
  rfl

--def solvev : Person  →  Person → Person  → Prop | A |  B|  C => (isKnight A ∧ statementA A) ∧ (isKnight B ∧ statmentB B) ∧ (isKnight C ∧ statmentC C)
--def solvevmod (A B C : Person):  Prop := (isKnight A ∧ statementA A) ∧ (isKnight B ∧ statmentB B) ∧ (isKnight C ∧ statmentC C)
--def tester : List (Person  × Person ×  Person):=[(knight, knave, normal),(knight, normal, knave),(knave, normal, knight),(normal,knight,knave),(normal,knave,knight),(knight,knight,knight),(knave,knave,knave),(normal,normal,normal)]
--
--#check List.permutations [normal,knave,knight]
---- not really showing the solution or reasoning, relying on lean to do it...
---- try all cases and subtitute
--def solution:= findSol(Person ×  Person ×  Person):=testpermutation.find(λ p, solve p.fst p.snd p.snd)

-/
