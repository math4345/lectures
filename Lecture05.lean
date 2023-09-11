import Mathlib.Tactic
import Mathlib.Data.Real.Basic

-- Math 4345: Lecture 5
--  _              _                     ___  ____  
-- | |    ___  ___| |_ _   _ _ __ ___   / _ \| ___| 
-- | |   / _ \/ __| __| | | | '__/ _ \ | | | |___ \ 
-- | |__|  __/ (__| |_| |_| | | |  __/ | |_| |___) |
-- |_____\___|\___|\__|\__,_|_|  \___|  \___/|____/ 
--                                                  

open Nat

#check (0 : ℝ)
#check (0 : ℕ)

#check Real.add_one_lt_exp_of_pos

-- Thanks Abel!
example : (Even 16) ∧ (Odd 19) := by
  apply And.intro
  use 8
  use 9
  norm_num

lemma add_zero' (a : ℕ) : a + zero = a := by rfl

#check Nat.add

lemma add_succ' (a b : ℕ) : (a + succ b) = succ (a + b) := by
  rfl

lemma zero_add' (a : ℕ) : zero + a = a := by
  induction a with 
  | zero => rfl
  | succ b ih => rw [add_succ, ih]

#check succ_add

lemma succ_add' (a b : ℕ) : (succ a + b) = succ (a + b) := by
  induction b with
  | zero => rw [add_zero']
  | succ _ ih => rw [add_succ, ih, add_succ]

#check add_comm

lemma add_comm' (a b : ℕ) : a + b = b + a := by
  induction' b with b ih
  rw [Nat.add_zero, Nat.zero_add]
  rw [add_succ, ih, succ_add]

#check Nat.mul_comm

-- let's review tactics so far in this course!

example : ∃ x : ℕ, x > 3 := by
  use 4
  norm_num

example : ∀ x : ℕ, x + 1 > x := by
  intro x
  linarith

example : ∃ x : ℕ, x > 2 ∧ x < 5 := by
  use 3
  apply And.intro
  <;> norm_num
  
example : ∀ x : ℕ, x ≥ 0 := by
  intro x
  exact nat.zero_le x

example : true ∨ false := by
  left
  trivial
