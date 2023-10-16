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

lemma lt_to_le : converges_to a b → converges_to' a b := by
  intro h
  intro ε hε 
  specialize h ε hε 
  rcases h with ⟨ N, h ⟩ 
  use N
  intros n hn
  specialize h n hn
  linarith

lemma le_to_lt : converges_to' a b → converges_to a b := by
  intros h ε hε
  rcases h (ε / 2) (by linarith) with ⟨ N, h ⟩ 
  use N
  intros n hn
  specialize h n hn
  linarith

lemma le_iff_lt : converges_to' a b ↔ converges_to a b :=
  Iff.intro le_to_lt lt_to_le 

section

variable (a b c : ℕ → ℝ)

lemma sandwich
  (hac : ∀ n, a n ≤ c n) 
  (hcb : ∀ n, c n ≤ b n) 
  (ℓ : ℝ)
  (ha : converges_to a ℓ) 
  (hb : converges_to b ℓ) : converges_to c ℓ := by
  intros ε hε 
  rcases ha ε hε with ⟨ Na, ha ⟩
  rcases hb ε hε with ⟨ Nb, hb ⟩

  use max Na Nb
  intros n hn

  have hna : n ≥ Na := le_of_max_le_left hn
  have hnb : n ≥ Nb := le_of_max_le_right hn
  clear hn

  specialize ha n hna
  specialize hb n hnb
  clear hna hnb
  
  have ha' := neg_lt_of_abs_lt ha
  have ha'' : ℓ - ε < a n := by linarith
  clear ha'

  have hb' : b n - ℓ < ε := lt_of_abs_lt hb
  have hb'' : b n < ℓ + ε := by linarith
  clear hb'

  specialize hac n
  specialize hcb n

  apply abs_sub_lt_iff.mpr 
  apply And.intro

  linarith
  linarith
  
end section

example (ε m : ℝ) (hε : ε > 0) (hm : m ≠ 0): (ε / |m| > 0) := 
 div_pos hε (abs_pos.mpr hm)

def diverges_to_infinity (a : ℕ → ℝ) :=
  ∀ (b : ℝ), ∃ (N : ℕ), ∀ n ≥ N, a n > b

-- The sum of convergent sequences converges to the sum
def s06p01 : converges_to (fun n => b) b := by sorry

-- The sum of convergent sequences converges to the sum
def s06p02 : converges_to a a' → converges_to b b'
  → converges_to (fun n => a n + b n) (a' + b') := by
  intro ha
  intro hb
  intros ε hε 
  
  specialize ha (ε / 2) (by linarith)
  specialize hb (ε / 2) (by linarith)
  
  rcases ha with ⟨ Na, ha ⟩
  rcases hb with ⟨ Nb, hb ⟩

  use max Na Nb
  intros n hn

  have hna : n ≥ Na := le_of_max_le_left hn
  have hnb : n ≥ Nb := le_of_max_le_right hn
  clear hn

  specialize ha n hna
  specialize hb n hnb
  clear hna hnb
  
  sorry  

def scaled_lim (m : ℝ) : converges_to a ℓ → 
  converges_to (fun n => m * (a n)) (m * ℓ) := by
  by_cases hm : m = 0
  
  rw [hm]
  ring_nf
  intro _
  exact s06p01

  intro h
  intros ε hε
  
  specialize h (ε / |m|) _
  
  apply div_pos hε
  apply abs_pos.mpr
  exact hm  

  ring_nf

  rcases h with ⟨ N, h ⟩
  use N

  intros n hn
  specialize h n hn
  
  have h1 := neg_lt_of_abs_lt h
  have h2 := lt_of_abs_lt h
  clear h

  apply abs_sub_lt_iff.mpr 
  apply And.intro

  by_cases hp : m > 0
  have habs : |m| = m := abs_of_pos hp
  rw [← habs]
  sorry -- use a calc block
  sorry
  sorry -- so apologetic!

-- lim_{n → ∞} aₙ = a' implies that 
-- lim_{n → ∞} (m aₙ + b) = m a' + b
def s06p03 (m b : ℝ) : converges_to a a'
  → converges_to (fun n => m * (a n) + b) (m * a' + b) := by
  intro ha
  have hb : converges_to (fun n => b) b := s06p01
  apply s06p02
  apply scaled_lim 
  exact ha
  exact hb

-- The sum of a convergent sequence and a divergent sequence diverges
def s06p04 : converges_to a a' → diverges_to_infinity b
  → diverges_to_infinity (fun n => a n + b n) := by sorry

def s06p05' : converges_to' (fun n => 1/n) 0 := by 
  intro ε 
  intro hε
  use Nat.ceil (1 / ε)
  intro n
  intro hn
  ring_nf
  have hr : (1 / ε) > 0
  exact one_div_pos.mpr hε
  have hpos : Nat.ceil (1 / ε) > 0
  apply Nat.lt_ceil.mpr
  ring_nf 
  ring_nf at hr
  exact hr  
  have hpn : (↑n) > 0 := by linarith  
  have k : 1 / (n : ℝ) ≤ 1 / ⌈1 / ε⌉₊
 
  apply one_div_le_one_div_of_le
  exact Nat.cast_pos.mpr hpos
  exact Nat.cast_le.mpr hn  
  ring_nf at k

  have ha : |1 / (n : ℝ)| = 1 / (n : ℝ)
  apply abs_of_pos
  apply one_div_pos.mpr
  exact Nat.cast_pos.mpr hpn

  ring_nf at ha
  rw [ha]

  have : 1 / (↑⌈ε⁻¹⌉₊) ≤ 1 / (1/ε) 
  apply one_div_le_one_div_of_le
  ring_nf
  apply inv_pos.mpr
  exact hε
  ring_nf
  exact Nat.le_ceil ε⁻¹
  ring_nf at this

  have hf : (↑n)⁻¹ ≤ ε⁻¹⁻¹ 
  linarith

  have hee : ε⁻¹⁻¹ = ε := inv_inv ε 
  rw [hee] at hf

  exact hf

def s06p05 : converges_to (fun n => 1/n) 0 := le_to_lt s06p05'
