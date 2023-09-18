import Mathlib.Tactic

-- Math 4345: Lecture 11
--  _              _                    _ _ 
-- | |    ___  ___| |_ _   _ _ __ ___  / / |
-- | |   / _ \/ __| __| | | | '__/ _ \ | | |
-- | |__|  __/ (__| |_| |_| | | |  __/ | | |
-- |_____\___|\___|\__|\__,_|_|  \___| |_|_|
--                                          
-- 

-- This week's goal is to think through "term mode" and how this
-- differsn from the "tactics" we have been using.

example : Monotone (fun (x : ℝ) ↦ 2 * x) := by
  dsimp [Monotone]
  intro a b
  intro h
  linarith

example {f g : ℝ → ℝ} : Monotone f → Monotone g → Monotone ( fun x => f x + g x ) := by
  intro hf
  intro hg
  intro a b
  intro h
  sorry
  
def s04p09 (m : ℝ) (b : ℝ) : (m ≥ 0) → Monotone (fun x ↦ m * x + b) := by
  sorry

def s04p10 (b : ℝ) : Function.Surjective (fun x ↦ x + b) := by
  sorry

