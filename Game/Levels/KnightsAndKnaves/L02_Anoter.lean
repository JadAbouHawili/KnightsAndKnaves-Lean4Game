import Game.Metadata
--import Game.LevelLemmas.Logical
open Set

variable {K : Type}

World "KnightsAndKnaves"
Level 2

Title "lev 2"

Introduction "Hi"

--Raymond Smullyan, what is the name of this book, problem 28
Statement 
  --sets
  (Knight : Set K ) (Knave : Set K)
  (h : Knight ∩ Knave = ∅ )
  (h1 : Xor' (x ∈ Knight) (x ∈ Knave) ) 
  (h2: Xor' (y ∈ Knight)  (y ∈ Knave) )
  -- theres x and y, x says at least one of us is a knave
  --rules of the game, i.e knights tell the truth but knaves lie
  (stx : x ∈ Knight → (x ∈ Knight ∧  y ∈ Knave)
                    ∨ (x ∈ Knave ∧ y ∈ Knight)
                    ∨ (x ∈ Knave ∧ y ∈ Knave)  )
  (stnx : x ∈ Knave → ¬ ( (x ∈ Knight ∧  y ∈ Knave)
                    ∨ (x ∈ Knave ∧ y ∈ Knight)
                    ∨ (x ∈ Knave ∧ y ∈ Knave) ) )
--goal
  : x ∈ Knight ∧ y ∈ Knave:= by
  {

   --rw [Xor'] at h1
   --rw [Xor'] at h2
   --exact h1
   --rw [Eq.rfl h1 ( (x ∈ Knight ∧ x ∉ Knave)  ∨ (x ∈ Knave ∧ x ∉ Knight ) )] at h1
   --cases h1
   --cases h2

   -- no need to take two cases, explain to the user why!!!!
   cases h1 
   --cases h2
   
   have contr :=  stx h_1.left 
   rcases contr    

   exact h_2

   cases h_2 
   have contr2 := mem_inter h_1.left h_3.left 
   rw [h] at contr2
   contradiction


   have contr2 := mem_inter h_1.left h_3.left 
   rw [h] at contr2
   contradiction

   have contr := stnx h_1.left
   push_neg at contr
   have yK := contr.right.left h_1.left 
   have yk2 : y ∈ Knave := by {
     rw [Xor'] at h2
     cases h2 
     have contr2:= h_2.left
     contradiction

     exact h_2.left
   }
  
   have target := contr.right.right
   have helpp := contrapositive target
   push_neg at helpp
   have done := helpp yk2
   have := h_1.left
   contradiction
   --contrapose at target
   --push_neg
   --push_neg at target
   --contrapose target
   --push_neg at target
  }

-- rewriting, making it neat
theorem organized 
  --sets
  (Knight : Set K ) (Knave : Set K)
  (h : Knight ∩ Knave = ∅ )
  (h1 : Xor' (x ∈ Knight) (x ∈ Knave) ) 
  (h2: Xor' (y ∈ Knight)  (y ∈ Knave) )
  -- theres x and y, x says at least one of us is a knave
  --rules of the game, i.e knights tell the truth but knaves lie
  (stx : x ∈ Knight → (x ∈ Knight ∧  y ∈ Knave)
                    ∨ (x ∈ Knave ∧ y ∈ Knight)
                    ∨ (x ∈ Knave ∧ y ∈ Knave)  )
  (stnx : x ∈ Knave → ¬ ( (x ∈ Knight ∧  y ∈ Knave)
                    ∨ (x ∈ Knave ∧ y ∈ Knight)
                    ∨ (x ∈ Knave ∧ y ∈ Knave) ) )
--goal
  : x ∈ Knight ∧ y ∈ Knave:= by
{ 
cases h1 with
| inl h_1 => 
  obtain ⟨xKnight, xnKnave⟩ := h_1 
  have xTruth := stx xKnight
  cases xTruth with 
  | inl h_1 => exact h_1
  | inr h_1 => cases h_1 with 
               | inl h_1 =>
               obtain ⟨xKnave,yKnight⟩ := h_1 
               contradiction

               | inr h_1 => 
               obtain ⟨xKnave,yKnave⟩ := h_1 
               contradiction
  
| inr h_1 => 
  obtain ⟨xKnave, xnKnight⟩ := h_1  
  have xLie := stnx xKnave
  push_neg at xLie
  obtain ⟨notneeded,ynKnight,ynKnave⟩:= xLie 
  have yNKnight := ynKnight xKnave
  have yNKnave := ynKnave xKnave
  cases h2 with 
    | inl h_1 => 
      obtain ⟨yKnight,_⟩:= h_1 
      contradiction
    | inr h_1 =>
      obtain ⟨yKnave,_⟩:= h_1 
      contradiction

}
-- no sorryAX
#print axioms organized

example : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
--  constructor -- ⊢ ¬(P ∨ Q) ↔ (¬P ∧ ¬Q)

  -- instead of relying on comment, have lean check it
  show ¬(P ∨ Q) ↔ (¬P ∧ ¬Q); constructor
  · intro h     -- ⊢ ¬(P ∨ Q) → ¬P ∧ ¬Q
    constructor       -- ⊢ ¬P ∧ ¬Q
    · intro hp        -- ⊢ ¬P
      exact h (Or.inl hp)
    · intro hq        -- ⊢ ¬Q
      exact h (Or.inr hq)  
  
  · intro h    -- ⊢ ¬P ∧ ¬Q → ¬(P ∨ Q)
    intro h1 -- ⊢ ¬(P ∨ Q) 
    cases h1 with -- ⊢ False
    | inl h_1 => exact h.left h_1 
    | inr h_1 => exact h.right h_1 


 

example : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  constructor

  intro h
  constructor

  intro h1
  exact h (Or.inl h1)

  intro h1
  exact h (Or.inr h1)

  intro h
  intro h1
  cases h1
  exact h.left h_1
  exact h.right h_1

example : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  constructor
  · intro h
    constructor
    · intro h1
      exact h (Or.inl h1)
    · intro h1
      exact h (Or.inr h1)
  · intro h
    intro h1
    cases h1 with
    | inl h_1 => exact h.left h_1
    | inr h_1 => exact h.right h_1


example : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  constructor
  case mp =>
    intro h
    constructor
    case left =>
      intro h1
      exact h (Or.inl h1)
    case right =>
      intro h1
      exact h (Or.inr h1)
  case mpr =>
    intro h
    intro h1
    cases h1 with
    | inl h_1 => exact h.left h_1
    | inr h_1 => exact h.right h_1

example : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) where
  mp h := by
    constructor
    · intro p
      apply h
      exact .inl p
    · intro q
      apply h
      exact .inr q
  mpr h h' := by
    cases h' with
    | inl h' => exact h.1 h'
    | inr h' => exact h.2 h'


example : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) where
  mp h := by
    constructor
    · intro p
      apply h
      exact .inl p
    · intro q
      apply h
      exact .inr q
  mpr h h' := by
    cases h' with
    | inl h' => exact h.1 h'
    | inr h' => exact h.2 h'


example (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq


Conclusion "."

/- Use these commands to add items to the game's inventory. -/


-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq



