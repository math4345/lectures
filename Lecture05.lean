import Mathlib.Tactic

-- Math 4345: Lecture 5
--  _              _                     ___  ____  
-- | |    ___  ___| |_ _   _ _ __ ___   / _ \| ___| 
-- | |   / _ \/ __| __| | | | '__/ _ \ | | | |___ \ 
-- | |__|  __/ (__| |_| |_| | | |  __/ | |_| |___) |
-- |_____\___|\___|\__|\__,_|_|  \___|  \___/|____/ 
--                                                  

open Nat

-- Thanks Abel!
example : (Even 16) ∧ (Odd 17) := by
  apply And.intro
  use 8
  use 8
  norm_num

lemma add_zero' (a : ℕ) : a + zero = a := by rfl

lemma zero_add' (a : ℕ) : zero + a = a := by
  induction' a with a ih
  rfl
  have h2 : zero + (succ a) = succ (zero + a) :=
    by rfl
  rw [h2, ih]

lemma add_succ' (a b : ℕ) : (a + succ b) = succ (a + b) := by rfl

lemma succ_add' (a b : ℕ) : (succ a + b) = succ (a + b) := by
  induction' b with b ih
  rw [add_zero']
  rw [add_succ' (succ a)]
  rw [ih]
  rw [add_succ' a]

lemma add_comm' (a b : ℕ) : a + b = b + a := by
  induction' b with b ih
  rw [add_zero', zero_add']
  rw [add_succ' a]
  rw [ih]
  rw [succ_add']

#check Nat.mul_comm


-- let's review tactics so far in this course!

example : ∃ x : ℕ, x > 3 := by
  use 4
  norm_num

example : ∃ x : ℕ, x > 2 ∧ x < 5 := by
  use 3
  apply And.intro
  norm_num
  norm_num

example : ∀ x : ℕ, x ≥ 0 := by
  intro x
  exact nat.zero_le x

example : true ∨ false := by
  left
  trivial
