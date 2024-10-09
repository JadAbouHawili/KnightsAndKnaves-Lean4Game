import Game.Metadata


World "KnightsAndKnaves" 
Level 3

Title "" 

Introduction 
"
Suppose A says, 'I am a knave, but B is not.' 
What are A and B? 
"

/-
def Knight (A: Prop) :Prop:=A 
def Knave (A:Prop):Prop:= ¬A 
def A_stat(A_knave B_not_knave:Prop):Prop:=A_knave  ∧  B_knave
def A_knave(A_knave B_knave:Prop) : Prop :=Knave (A_stat A_knave B_knave:Prop) def A_Knight(A_knave B_knave : Prop):Prop := Knight (A_stat A_knave B_knave)

example: ∃ A_knave B_knave : Prop, A_knave ∧ B_knave := begin 
Knight (A : Prop) : Prop
Knave (A : Prop) : Prop
A_stat (A_knave B_knave : Prop) : Prop
-/ 

Statement
  --sets
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{h2: B ∈ Knight ∨ B ∈ Knave }
-- like i am a knave
{stA : A ∈ Knight  ↔ (A ∈ Knave  ∧  B ∉ Knave) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave  ∧  B ∉ Knave) }
  :  A ∈ Knave ∧ B ∈ Knave:= by

  {
  rcases h1 with AKnight|AKnave
  · 
    have AKnBK:= stA.mp AKnight
    -- contradiction
    exfalso
    exact disjoint h AKnight AKnBK.left
  · have := stAn.mp AKnave
    rw [not_and_or] at this
    -- looks like a good time to introduce simp
    simp [AKnave] at this
    --have := notleft_right  this (by push_neg; exact AKnave)
    constructor
    assumption
    assumption

    --cases this
    --contradiction
    --push_neg at h_1
    --constructor
    --assumption ; assumption
    --have AKnBK:= stA.mp AKnight

  }





Conclusion 
"
"

NewTactic push_neg simp
NewTheorem not_and_or
