import Mathlib.Tactic
import Mathlib.Data.Nat.Basic

-- Math 4345: Lecture 2
--  _              _                     ___ ____  
-- | |    ___  ___| |_ _   _ _ __ ___   / _ \___ \ 
-- | |   / _ \/ __| __| | | | '__/ _ \ | | | |__) |
-- | |__|  __/ (__| |_| |_| | | |  __/ | |_| / __/ 
-- |_____\___|\___|\__|\__,_|_|  \___|  \___/_____|
--                                                 

-------------------------------------------------------
-- Let's review what we learned last time

section

example : (2 + 3) = 5 := by
  rfl

example (x : ℕ) : x + 1 = 1 + x := by
  sorry

end section

-------------------------------------------------------
-- Lean is a programming language

def double (x : ℕ) := x + x

example : double 3 = 6 := by rfl

#eval 5 + 5

#eval double 8

-------------------------------------------------------
-- The theme in Week 1 is "natural numbers."

section

-- Type the "fancy N" by typing \N
variable (x y z : ℕ)

#check x

-- We can invoke commutativity and associativity 
example : x * y = y * x := by 
  rw [mul_comm]
  
example : (x * y) * z = x * (y * z) := by 
  rw [mul_assoc]

example : x + y = y + x := by 
  rw [add_comm]

example : (x + y) + z = x + (y + z) := by 
  sorry 

example : x * y * z = z * (x * y) := by 
  sorry
  
example : x * y * z = z * x * y := by 
  sorry

example : x * (y + z) = x * y + x * z := by 
  rw [mul_add]
  
example (a b : ℕ) : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by
  sorry

end section

-------------------------------------------------------
-- We can also prove implications

example (x y : ℕ) (h : x = y) : x + 1 = y + 1 := by
  rw [h]

example (x y : ℕ) : (x = y) → (x + 1 = y + 1) := by
  intro h
  rw [h]

-------------------------------------------------------
-- We can name theorems and use them later

section

lemma add_double (x : ℕ) : x + x = 2 * x := by
  rw [← one_mul x]
  rw [← add_mul]
  rw [one_mul]
  norm_num  

example (x : ℕ) : x + x + x = 2 * x + x := by
  rw [add_double]

end section

-------------------------------------------------------
-- Other tactics to try: apply
