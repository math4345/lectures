import Mathlib.Tactic
import Mathlib.Data.Nat.Basic

-- Math 4345: Lecture 3
--  _              _                     ___ _____ 
-- | |    ___  ___| |_ _   _ _ __ ___   / _ \___ / 
-- | |   / _ \/ __| __| | | | '__/ _ \ | | | ||_ \ 
-- | |__|  __/ (__| |_| |_| | | |  __/ | |_| |__) |
-- |_____\___|\___|\__|\__,_|_|  \___|  \___/____/ 
--                                                 
-- 

def fib : (n : ℕ) → ℕ := fun 
  | 0 => 0
  | 1 => 1
  | (Nat.succ (Nat.succ n)) =>
    (fib n) + (fib (Nat.succ n)) 

inductive mynat where
  | zero : mynat
  | succ (n : mynat) : mynat
deriving Repr

namespace mynat

def add : mynat → mynat → mynat := fun
  | m, zero        => m
  | m, succ n      => succ (add m n)

def add_zero (n : mynat) : (add n zero) = n := by rfl

def zero_add (n : mynat) : (add zero n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => 
    rw [add]
    rw [ih]
      
def zero_add' : (n : mynat) → (add zero n) = n := fun
  | zero => rfl
  | succ n => by simp [add, zero_add']
  
