import Mathlib.Tactic

-- Math 4345: Lecture 15
--  _              _                    _ ____  
-- | |    ___  ___| |_ _   _ _ __ ___  / | ___| 
-- | |   / _ \/ __| __| | | | '__/ _ \ | |___ \ 
-- | |__|  __/ (__| |_| |_| | | |  __/ | |___) |
-- |_____\___|\___|\__|\__,_|_|  \___| |_|____/ 
--                                              
-- 

-- recall our definition from last time
def converges_to (a : ℕ → ℝ) (ℓ : ℝ) :=
  ∀ ε > 0, ∃ (N : ℕ), ∀ n ≥ N, |a n - ℓ| < ε

def f : ℕ → ℝ 
 | 0 => 17
 | 1 => 15
 | (_ + 1) + 1 => 2

lemma help_me : ∀ n ≥ 2, f n = 2 := by
  intro n
  intro hn
  exact match n with
  | 0 => by tauto
  | 1 => by tauto
  | (m + 2) => by rfl

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

def eventually_constant (a : ℕ → ℝ) (c : ℝ) := 
  ∃ (N : ℕ), ∀ n ≥ N, a n = c

lemma ec_f : eventually_constant f 2 := by
  use 2
  intros n hn
  exact help_me n hn

lemma ec_lim (a : ℕ → ℝ) (ℓ : ℝ): eventually_constant a ℓ → converges_to a ℓ := by
  rintro ⟨ N, h ⟩ ε hε 
  use N
  intros n hn
  specialize h n hn
  rw [h] -- this is the "key idea"
  norm_num
  assumption  

example : converges_to f 2 := ec_lim f 2 ec_f

example (a : ℕ → ℝ) (b : ℕ → ℝ) (ℓ₁ ℓ₂ : ℝ) :
  eventually_constant a ℓ₁ →
  eventually_constant b ℓ₂ → 
  eventually_constant (fun n => a n + b n) (ℓ₁ + ℓ₂) := by sorry

example : converges_to a 0 → converges_to (fun n => 2 * a n) 0 := by
  intro h
  unfold converges_to
  intros ε hε
  unfold converges_to at h
  specialize h (ε/2) (half_pos hε)
  rcases h with ⟨ N, h ⟩ 
  use N
  intros n hn
  specialize h n hn
  ring_nf
  calc |a n * 2| = |a n + a n| := by ring_nf
    _ ≤ |a n| + |a n| := by apply abs_add
    _ = |a n - 0| + |a n - 0| := by ring_nf
    _ < (ε / 2) + (ε / 2) := add_lt_add h h
    _ = ε := by ring_nf
