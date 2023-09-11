import Mathlib.Tactic

-- Math 4345: Lecture 8
--  _              _                     ___   ___  
-- | |    ___  ___| |_ _   _ _ __ ___   / _ \ ( _ ) 
-- | |   / _ \/ __| __| | | | '__/ _ \ | | | |/ _ \ 
-- | |__|  __/ (__| |_| |_| | | |  __/ | |_| | (_) |
-- |_____\___|\___|\__|\__,_|_|  \___|  \___/ \___/ 
--                                                  
-- 

-- This week's theme is "logic" and "propositions"

-- goal: the "by_contra" tactic 

example : ∀ (ε : ℝ), (0 < ε) → (0 < 1 / ε) := by
  intro ε
  intro h
  apply one_div_pos.mpr
  exact h

section

variable (P Q : Prop) 

def np_and_nq_implies_not_porq : (¬ P) ∧ (¬ Q) → ¬ (P ∨ Q) := by
  intro h
  rcases h with ⟨ hp, hq ⟩ 
  intro h
  rcases h with p|q
  apply hp
  exact p
  apply hq
  exact q

def not_porq_implies_np_and_nq : ¬(P ∨ Q) → (¬ P) ∧ (¬ Q) := by
  intro h
  apply And.intro
  
  by_contra hp
  apply h
  left
  exact hp

  by_contra hq
  apply h
  right
  exact hq
  
def not_porq_iff_np_and_nq : ¬(P ∨ Q) ↔ (¬ P) ∧ (¬ Q) := by
  constructor
  apply not_porq_implies_np_and_nq
  apply np_and_nq_implies_not_porq

end section

variable {α : Type} (P : α → Prop)

example : (¬ ∀ x, P x) → ∃ x, ¬ P x := by
  intro h
  by_contra h'
  apply h
  intro x
  by_contra h''
  apply h'
  use x 

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
