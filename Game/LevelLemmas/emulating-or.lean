axiom isKnight (A : Type) :  Prop
axiom isKnave (A : Type) :  Prop
inductive Inhabitant (A : Type) where
  | knight (h : isKnight A) 
  | knave (h : isKnave A)

-- doing inductive setup is reduntant because person_cases
inductive Person (A : Prop) where
  | knight (h : A) : (Person A)
  | knave (h : ¬A) : Person A

