import Mathlib.Tactic

-- Math 4345: Lecture 18
--  _              _                    _  ___  
-- | |    ___  ___| |_ _   _ _ __ ___  / |( _ ) 
-- | |   / _ \/ __| __| | | | '__/ _ \ | |/ _ \ 
-- | |__|  __/ (__| |_| |_| | | |  __/ | | (_) |
-- |_____\___|\___|\__|\__,_|_|  \___| |_|\___/ 
--                                              
-- 

-- 

example : 3 ∈ {x : ℤ | x * x > 2 } := by
  dsimp
  norm_num

example : 1 ∉ {x : ℤ | x * x > 2 } := by
  dsimp
  norm_num

example : {x : ℤ | x * x > 3 } ⊆ {x : ℤ | x * x > 2 } := by
  intro n
  intro hn
  dsimp at hn
  dsimp
  linarith

example : {x : ℤ | Odd x} = {x : ℤ | ∃ k, x = 2 * k + 1 } := by
  ext x
  constructor
  dsimp
  unfold Odd
  intro h
  assumption
  unfold Odd
  intro h
  assumption  

section

#check (Set.univ : Set ℤ)

example : 3 ∈ (Set.univ : Set ℤ) := trivial

variable (A B C : Set ℤ)

example : A ∩ (B ∪ C) ⊆ A := by
  intro x
  intro hx
  rcases hx with ⟨ ha, hbc ⟩
  assumption

end section

example : {x : ℚ | x * x = 2 } = ∅ := by
  sorry
  