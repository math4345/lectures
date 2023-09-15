import Mathlib.Tactic

-- Math 4345: Lecture 10
--  _              _                    _  ___  
-- | |    ___  ___| |_ _   _ _ __ ___  / |/ _ \ 
-- | |   / _ \/ __| __| | | | '__/ _ \ | | | | |
-- | |__|  __/ (__| |_| |_| | | |  __/ | | |_| |
-- |_____\___|\___|\__|\__,_|_|  \___| |_|\___/ 
--                                              
-- 

-- new tactic: specialize

def bounded (f : ℝ → ℝ) := ∃ b, ∀ x, f x ≤ b

example {f : ℝ → ℝ } : bounded f → bounded ( fun x => 2 * f x ) := by
  dsimp [bounded]
  intro h
  rcases h with ⟨ b, h ⟩ 
  use 2 * b
  intro x
  specialize h x
  linarith

-- the squaring function is continuous at zero
example : ∀ (ε : ℝ), (0 < ε) → ∃ (δ : ℝ), (0 < δ) ∧ ∀ (x : ℝ), abs x < δ → abs (x * x) < ε := by
  intro ε 
  intro hε
  use min ε 1

  apply And.intro

  apply lt_min
  exact hε
  norm_num

  intro x
  intro hx
  
  have h' : |x| < ε ∧ |x| < 1 := Iff.mp lt_min_iff hx
  rcases h' with ⟨ h, h1 ⟩ 

  have h'' : |x| * |x| < ε * 1
  apply mul_lt_mul'
  linarith
  linarith
  apply abs_nonneg
  exact hε

  rw [abs_mul]  
  ring_nf at h''
  ring_nf
  exact h''



