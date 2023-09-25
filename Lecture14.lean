import Mathlib.Tactic

-- Math 4345: Lecture 14
--  _              _                    _ _  _   
-- | |    ___  ___| |_ _   _ _ __ ___  / | || |  
-- | |   / _ \/ __| __| | | | '__/ _ \ | | || |_ 
-- | |__|  __/ (__| |_| |_| | | |  __/ | |__   _|
-- |_____\___|\___|\__|\__,_|_|  \___| |_|  |_|  
--                                               
-- 

-- This is our first discussion of "sequences"

-- Have you seen this definition before?

-- a sequence is a function from ℕ to ℝ 
-- we write the input as a subscript

-- write aₙ for the sequence a applied to n.

def b : ℕ → ℝ := fun n => 2*n

#eval b 5 -- write b 5 for b₅

-- What does it say in words?
def converges_to (a : ℕ → ℝ) (ℓ : ℝ) :=
  ∀ ε > 0, ∃ (N : ℕ), ∀ n ≥ N, |a n - ℓ| < ε

example (a : ℝ) : converges_to (fun _ => a) a := by 
  sorry

-- `fun n => a` is the constant sequence aₙ = a.
lemma const_converge (a : ℝ) : converges_to (fun _ => a) a := by 
  -- unfold converges_to
  intro ε
  intro hε
  use 100
  intro n
  intro _
  rw [sub_self, abs_zero] -- alternatively, ring_nf and norm_num
  assumption -- or linarith
  -- exact hε 
  -- assumption
  
#print const_converge

def f : ℕ → ℝ 
 | 0 => 17
 | 1 => 15
 | _ => 2

lemma help_me : ∀ n ≥ 2, f n = 2 := by
  intro n
  rcases n with _|n
  tauto
  rcases n
  tauto
  intro _
  rfl

example : converges_to f 2 := by 
  intro ε
  intro hε
  use 2
  intro n
  intro hn
  rw [help_me]
  case h =>
    norm_num
    exact hε 
  case h.a =>
    exact hn


