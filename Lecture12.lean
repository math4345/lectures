import Mathlib.Tactic

-- Math 4345: Lecture 12
--  _              _                    _ ____  
-- | |    ___  ___| |_ _   _ _ __ ___  / |___ \ 
-- | |   / _ \/ __| __| | | | '__/ _ \ | | __) |
-- | |__|  __/ (__| |_| |_| | | |  __/ | |/ __/ 
-- |_____\___|\___|\__|\__,_|_|  \___| |_|_____|
--                                              
-- 

section

variable (P Q R : Prop)

example : P → (P ∨ Q) := by
  intro h
  left
  exact h

example : P → (P ∨ Q) := fun h => Or.inl h

example : Q → (P ∨ Q) := fun h => Or.inr h

-- this is the "left injection" from P to P ∨ Q
example : P → (P ∨ Q) := Or.inl

-- this is the "right injection" from Q to P ∨ Q
example : Q → (P ∨ Q) := Or.inr

example : (P ∨ Q) → (P ∨ Q) := fun h => h

example : (P ∨ Q) → (Q ∨ P) := by
  intro h
  rcases h with hp|hq
  exact Or.inr hp
  exact Or.inl hq

example : (P ∨ P) → P := fun
  | Or.inl h => h
  | Or.inr h => h

example : (P ∨ Q) → (Q ∨ P) := sorry

end section

-- new tactic: calc

section

example (x y : ℝ) (h1 : x + y = 8) (h2 : x * y = 16) : x = 4 := by
  have h : (x - y)^2 = 0 :=
    calc (x - y)^2 = (x + y) ^ 2 - 4 * (x * y) := by ring
                 _ = 8 ^ 2 - 4 * 16 := by rw [h1, h2]
                 _ = 0 := by norm_num
  have h' : x - y = 0 := Iff.mp sq_eq_zero_iff h
  linarith

example (x y : ℝ) : x * y ≤ ( (x + y) / 2 ) ^ 2 := by
  have h : ((x - y)/2)^2 ≥ 0 := sq_nonneg ((x - y)/2)
  exact
    calc x * y 
      ≤ x * y + ((x - y)/2)^2 := le_add_of_nonneg_right h
      _ = ((x + y)/2) ^ 2 := by ring

end section

-- Let's try a bit more "programming" in Lean

section

inductive list where
  | nil : list
  | cons (x : ℕ) (xs : list) : list

open list

#check nil

#check cons 5 (cons 3 nil)

def len : list → ℕ := fun
  | nil => 0
  | cons _ xs => 1 + len xs

def append : list → list → list := fun  

end section

