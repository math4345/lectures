import Mathlib.Tactic

-- Math 4345: Lecture 16
--  _              _                    _  __   
-- | |    ___  ___| |_ _   _ _ __ ___  / |/ /_  
-- | |   / _ \/ __| __| | | | '__/ _ \ | | '_ \ 
-- | |__|  __/ (__| |_| |_| | | |  __/ | | (_) |
-- |_____\___|\___|\__|\__,_|_|  \___| |_|\___/ 
--                                              
-- 

-- recall yet again our definition from last time
def converges_to (a : ℕ → ℝ) (ℓ : ℝ) :=
  ∀ ε > 0, ∃ (N : ℕ), ∀ n ≥ N, |a n - ℓ| < ε

def converges_to' (a : ℕ → ℝ) (ℓ : ℝ) :=
  ∀ ε > 0, ∃ (N : ℕ), ∀ n ≥ N, |a n - ℓ| ≤ ε

lemma le_to_lt : converges_to' a b → converges_to a b := by
  sorry
  