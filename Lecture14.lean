import Mathlib.Tactic

-- Math 4345: Lecture 14
--  _              _                    _ _  _   
-- | |    ___  ___| |_ _   _ _ __ ___  / | || |  
-- | |   / _ \/ __| __| | | | '__/ _ \ | | || |_ 
-- | |__|  __/ (__| |_| |_| | | |  __/ | |__   _|
-- |_____\___|\___|\__|\__,_|_|  \___| |_|  |_|  
--                                               
-- 

-- This is our first discussion of "sequences

-- Have you seen this definition before?

-- What does it say in words?
def converges_to (a : ℕ → ℝ) (ℓ : ℝ) :=
  ∀ ε > 0, ∃ (N : ℕ), ∀ n ≥ N, |a n - ℓ| < ε

example : converges_to (fun n => a) a := by sorry

def f : ℕ → ℝ 
 | 0 => 17
 | 1 => 15
 | _ => 2

example : converges_to f 2 := by sorry

example : converges_to a 0 → converges_to (fun n => 2 * a n) 0 := by sorry

