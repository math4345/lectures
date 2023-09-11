import Mathlib.Tactic

-- Math 4345: Lecture 9
--  _              _                     ___   ___  
-- | |    ___  ___| |_ _   _ _ __ ___   / _ \ / _ \ 
-- | |   / _ \/ __| __| | | | '__/ _ \ | | | | (_) |
-- | |__|  __/ (__| |_| |_| | | |  __/ | |_| |\__, |
-- |_____\___|\___|\__|\__,_|_|  \___|  \___/   /_/ 
--                                                  
-- 

-- new tactic: specialize

section

variable {α : Type} (P : α → Prop)

example : (¬ ∀ x, P x) → ∃ x, ¬ P x := by
  intro h
  by_contra h'
  apply h
  intro x
  by_contra h''
  apply h'
  use x 

-- Can you invent similar examples?

end section

section

def bounded (f : ℝ → ℝ) := ∃ b, ∀ x, f x ≤ b

example {f : ℝ → ℝ } : bounded f → bounded ( fun x => 2 * f x ) := by
  dsimp [bounded]
  intro h
  rcases h with ⟨ b, h ⟩ 
  use 2 * b
  intro x
  specialize h x
  linarith

end section

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
