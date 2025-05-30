/-
A is a knight. A says that B is a knave. Prove that B is a knave.
-/
example {A B : Islander} (hA : A.isKnight) (hAB : A said B.isKnave) : B.isKnave := by
  exact knight_said hAB hA
