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

def eventually_constant (a : ℕ → ℝ) := 
  ∃ (N : ℕ) (c : ℝ), ∀ n ≥ N, a n = c

example (a : ℕ → ℝ) : eventually_constant a → ∃ ℓ, converges_to a ℓ := by
  intro h
  rcases h with ⟨ w, c, h ⟩
  use c
  intro ε 
  intro hε 
  use w
  intro n
  intro hn
  specialize h n
  specialize h hn
  rw [h]
  norm_num
  exact hε 

example : converges_to a 0 → converges_to (fun n => 2 * a n) 0 := by
  intro h
  intro ε 
  intro hε 
  specialize h (ε/2) (by linarith) 
  rcases h with ⟨ N, h ⟩
  use N
  intro n
  specialize h n
  intro hn
  specialize h hn
  ring_nf
  calc |a n * 2| = |a n + a n| := by ring_nf
    _ ≤ |a n| + |a n| := abs_add (a n) (a n)
    _ = |a n - 0| + |a n - 0| := by ring_nf
    _ < (ε / 2) + (ε / 2) := by exact add_lt_add h h
    _ = ε := by ring

def converges_to' (a : ℕ → ℝ) (ℓ : ℝ) :=
  ∀ ε > 0, ∃ (N : ℕ), ∀ n ≥ N, |a n - ℓ| ≤ ε

lemma le_to_lt : converges_to' a b → converges_to a b := by

