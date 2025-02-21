import Game.Metadata

-- without parameter

inductive Person 
| knight : Person 
| knave : Person 
| normal : Person 
open Person

axiom Said : Person → Prop → Prop
notation A " said " P:200 => Said A P
def isKnight (A : Person) := (A = knight)
def isKnave (A : Person) := (A = knave)
/-
knight said isKnave knight
-/
axiom knight_said {P : Prop} : knight said P → P
axiom knave_said {P : Prop} : knave said P → ¬P
-- inductive would work like this, A : Person then A=knight
example  (A B C : Person)  
-- to represent statements, go to ↔ or said
-- then other stuff follows
{stA : A said (isKnave A)}
: False := by 
  cases A 
  have AKnave := knight_said stA
  contradiction

  -- AnKnave says, it is not true that knave is a knave
  have AnKnave := knave_said stA
  contradiction

  sorry 
example (P : Bool) : 2=2 := by 
  cases P
  rfl
  rfl
--  #check statementA 
--  --#print statementA
--
--  have stAatA:= statementA 
--  -- not self contained, not easy to reuse


def isKnight (A : Person) :=
    match A with 
    | knight => True
    | _=> false
example {A : Person}  : 2=2 := by 
  cases A
  repeat sorry


inductive Weekday where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
deriving Repr
open Weekday

namespace Weekday
def next (d : Weekday) : Weekday :=
 match d with
 | sunday    => monday
 | monday    => tuesday
 | tuesday   => wednesday
 | wednesday => thursday
 | thursday  => friday
 | friday    => saturday
 | saturday  => sunday
def previous (d : Weekday) : Weekday :=
 match d with
 | sunday    => saturday
 | monday    => sunday
 | tuesday   => monday
 | wednesday => tuesday
 | thursday  => wednesday
 | friday    => thursday
 | saturday  => friday

def next_previous (d : Weekday) : next (previous d) = d := by
  cases d <;> rfl

def numberOfDay (d : Weekday) : Nat :=
match d with
  | sunday    => 1
  | monday    => 2
  | tuesday   => 3
  | wednesday => 4
  | thursday  => 5
  | friday    => 6
  | saturday  => 7

axiom isKnight2 (A : Type) :  Prop
axiom isKnave2 (A : Type) :  Prop
inductive Inhabitant (A : Type) where
  | knight (h : isKnight2 A) 
  | knave (h : isKnave2 A)

--example {A : Type} (h : Inhabitant A)
-- doing inductive setup is reduntant because person_cases
inductive Or2 (a b : Prop) : Prop where
  | inl (h : a) : Or2 a b
  /-- `Or.inr` is "right injection" into an `Or`. If `h : b` then `Or.inr h : a ∨ b`. -/
  | inr (h : b) : Or2 a b

/-- Alias for `Or.inl`. -/
theorem Or.intro_left2 (b : Prop) (h : a) : Or a b :=
  Or.inl h

/-- Alias for `Or.inr`. -/
theorem Or.intro_right2 (a : Prop) (h : b) : Or a b :=
  Or.inr h
#check Or

example(d : Weekday) :2=2 := by
    cases d
    repeat sorry
--def isKnave : Person A → Prop | knight => false | knave => true | normal => false 
--def isNormal : Person A → Prop | knight  => false | knave  => false | normal  => true 
--
---- with parameter, resolve issues...
--inductive Person (A : Type)
--| knight (h : A.isKnight) : Person A
--| knave (h : A.isKnave) : Person A
--| normal : Person A
--
--def isKnight {A  : Type} (Person A) := 
--  match A with
--  | knight => true | knave => false | normal => false 

example {A : Type} {h : Person A}  : 2=2 := by 
  cases h
  sorry

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
example {A : Prop} {hA : Islander2 A} : 
  

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
    
-- evalutes to whether stA true or not
-- any person here not just A
def statementA : Person → Prop | p  => match p with | knight => isNormal knight | knave =>(isNormal knave) | normal => true 
--def statementAmod := (isKnight A) →  (isNormal A)
def statmentB: Person  → Prop | p => match p with | knight => statementA knight | knave => ¬ (statementA knave)|normal => false -- here we don't know, B being normal we don't know if A's st is true or false|--normal => statementA normal
def statmentC: Person  → Prop | p => match p with | knight => ¬ (isNormal knight ) | knave => ¬ (isNormal knave) | normal => true


--def solvev : Person  →  Person → Person  → Prop | A |  B|  C => (isKnight A ∧ statementA A) ∧ (isKnight B ∧ statmentB B) ∧ (isKnight C ∧ statmentC C)
--def solvevmod (A B C : Person):  Prop := (isKnight A ∧ statementA A) ∧ (isKnight B ∧ statmentB B) ∧ (isKnight C ∧ statmentC C)
--def tester : List (Person  × Person ×  Person):=[(knight, knave, normal),(knight, normal, knave),(knave, normal, knight),(normal,knight,knave),(normal,knave,knight),(knight,knight,knight),(knave,knave,knave),(normal,normal,normal)]
--

-/
example (A : Person A) ( h : A = normal): isNormal A := 
  by 
  rw [h]
  unfold isNormal
  rfl

#check List.permutations [1,2,3]
#check List.permutations [normal,knave,knight]
