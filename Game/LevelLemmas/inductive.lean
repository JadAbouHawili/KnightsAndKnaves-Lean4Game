import Game.Metadata

inductive Person 
| knight : Person 
| knave : Person 
| normal : Person 

open Person
-- cases would replace A : Person with knight,knave,normal
example {A : Person} : A=knight := by 
  cases A
  rfl 
  sorry
  sorry

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

def isKnight2 (A : Person) :=
    match A with 
    | knight => True
    | _=> false
#check isKnight2

/-- Alias for `Or.inl`. -/
theorem Or.intro_left2 (b : Prop) (h : a) : Or a b :=
  Or.inl h

/-- Alias for `Or.inr`. -/
theorem Or.intro_right2 (a : Prop) (h : b) : Or a b :=
  Or.inr h
#check Or

open Person 

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


#check List.permutations [1,2,3]
#check List.permutations [normal,knave,knight]
