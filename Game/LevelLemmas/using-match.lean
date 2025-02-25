inductive Person 
| knight : Person 
| knave : Person 
-- saysing A is a knight
-- A = knight

open Person

namespace Person
def isKnave  {A : Person} : Prop :=
  match A with 
|knight => false 
| knave => true


def isKnight  {A : Person} : Prop :=
  match A with 
|knight => true 
| knave => false


variable {A : Person}
def statementC : Prop := 
  match A with 
  | 
  knight => (A.isKnave) | 
  knave => ¬ (A.isKnave) 
#check statementC
example {h : @statementC A} :False := by 
  unfold statementC at h
  cases A
  simp at h
  · 
    -- in this case A , is a knight but i can't see that
    contradiction
  · sorry

