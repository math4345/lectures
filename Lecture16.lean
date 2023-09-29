import Mathlib.Tactic

-- Math 4345: Lecture 16
--  _              _                    _  __   
-- | |    ___  ___| |_ _   _ _ __ ___  / |/ /_  
-- | |   / _ \/ __| __| | | | '__/ _ \ | | '_ \ 
-- | |__|  __/ (__| |_| |_| | | |  __/ | | (_) |
-- |_____\___|\___|\__|\__,_|_|  \___| |_|\___/ 
--                                              
-- 

-- https://github.com/leanprover/lean4/releases/tag/v4.1.0

-- recall yet again our definition from last time
def converges_to (a : ℕ → ℝ) (ℓ : ℝ) :=
  ∀ ε > 0, ∃ (N : ℕ), ∀ n ≥ N, |a n - ℓ| < ε

def converges_to' (a : ℕ → ℝ) (ℓ : ℝ) :=
  ∀ ε > 0, ∃ (N : ℕ), ∀ n ≥ N, |a n - ℓ| ≤ ε

lemma le_to_lt : converges_to' a b → converges_to a b := by
  sorry

section

variable (a b c : ℕ → ℝ)

lemma sandwich
  (hac : ∀ n, a n ≤ c n) 
  (hcb : ∀ n, c n ≤ b n) 
  (ℓ : ℝ)
  (ha : converges_to a ℓ) 
  (hb : converges_to b ℓ) : converges_to c ℓ := by
  intro ε
  intro hε
  specialize ha ε hε
  specialize hb ε hε 
  rcases ha with ⟨ Na, ha ⟩
  rcases hb with ⟨ Nb, hb ⟩
  use max Na Nb
  intro n
  intro hn
  have hna : n ≥ Na := le_of_max_le_left hn
  have hnb : n ≥ Nb := le_of_max_le_right hn
  specialize ha n hna
  specialize hb n hnb
  clear hn hna hnb
  have ha' := neg_lt_of_abs_lt ha
  have ha'' : ℓ - ε < a n := by linarith
  have hb' : b n - ℓ < ε := lt_of_abs_lt hb
  have hb'' : b n < ℓ + ε := by linarith
  specialize hac n
  specialize hcb n
  have hc' : ℓ - ε < c n := by linarith
  have hc : c n < ℓ + ε := by linarith
  have hc'' : c n - ℓ < ε := by linarith
  have hc''' : c n - ℓ > -ε := by linarith
  apply abs_sub_lt_iff.mpr 
  apply And.intro
  linarith
  linarith

end section
