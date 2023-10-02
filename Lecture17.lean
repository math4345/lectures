import Mathlib.Tactic

-- Math 4345: Lecture 17
--  _              _                    _ _____ 
-- | |    ___  ___| |_ _   _ _ __ ___  / |___  |
-- | |   / _ \/ __| __| | | | '__/ _ \ | |  / / 
-- | |__|  __/ (__| |_| |_| | | |  __/ | | / /  
-- |_____\___|\___|\__|\__,_|_|  \___| |_|/_/   
--                                              
-- 

-- the overall theme this week is inequalities

example : ∃! (x : ℝ), x + 1 = 3 := by
  use 2
  constructor
  norm_num
  intro y
  norm_num
  intro hy
  linarith

example (x : ℝ) : 0 ≤ x * x := mul_self_nonneg x

lemma inequality1 (x y : ℝ) :
  x * y ≤ (x ^ 2 + y ^ 2) / 2 := by
  have h := 
    calc x ^ 2 + y ^ 2 - 2 * x * y = (x - y) ^ 2 := by ring
      _ = (x - y) * (x - y) := by ring
      _ ≥ 0 := mul_self_nonneg (x - y) -- this is the key step
  linarith

lemma inequality2 (x y : ℝ) :
  - (x * y) ≤ (x ^ 2 + y ^ 2) / 2 := by
  have h := 
    calc x ^ 2 + y ^ 2 + 2 * x * y = (x + y) ^ 2 := by ring
      _ = (x + y) * (x + y) := by ring
      _ ≥ 0 := mul_self_nonneg (x + y) -- this is the key step
  linarith

example (x y : ℝ) : |x * y| ≤ (x ^ 2 + y ^ 2) / 2 := by
  apply abs_le'.mpr
  constructor
  apply inequality1
  apply inequality2

example (x y : ℝ) : |x * y| ≤ (x ^ 2 + y ^ 2) / 2 := by
  apply abs_le'.mpr
  constructor
  exact inequality1 x y
  have h := inequality1 (-x) y
  norm_num at h
  assumption

-- this is "commutativity" for min
example (x y : ℝ) : min x y = min y x := by
  apply le_antisymm
  apply le_min
  apply min_le_right
  apply min_le_left
  apply le_min
  apply min_le_right
  apply min_le_left

example (x y : ℝ) : min x y = min y x := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example (x y : ℝ) : min x y = min y x := by
  have h : (a b : ℝ) → min a b ≤ min b a := by
    intros a b   
    apply le_min
    apply min_le_right
    apply min_le_left
  exact le_antisymm (h x y) (h y x)

example (x y : ℝ) : min x y = min y x := 
  let h (a b : ℝ) : min a b ≤ min b a := 
    le_min (min_le_right a b) (min_le_left a b)
  le_antisymm (h x y) (h y x)

-- this is "associativity" for min
example (x y z : ℝ) : min x (min y z) = min (min x y) z := by
  apply le_antisymm
  apply le_min
  apply le_min
  apply min_le_left
  apply min_le_of_right_le
  apply min_le_left
  apply min_le_of_right_le
  apply min_le_right
  apply le_min
  apply min_le_of_left_le
  apply min_le_left
  apply le_min
  apply min_le_of_left_le
  apply min_le_right
  apply min_le_right
