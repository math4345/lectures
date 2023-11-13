import Mathlib.Tactic

-- Math 4345: Lecture 31
--  _              _                    _____ _
-- | |    ___  ___| |_ _   _ _ __ ___  |___ // |
-- | |   / _ \/ __| __| | | | '__/ _ \   |_ \| |
-- | |__|  __/ (__| |_| |_| | | |  __/  ___) | |
-- |_____\___|\___|\__|\__,_|_|  \___| |____/|_|
--
--

variable {X : Type*}
variable [MetricSpace X] (x y z : X)

#check (dist x y : ℝ)
#check (dist_eq_zero : dist x y = 0 ↔ x = y)
#check (dist_nonneg : 0 ≤ dist x y)
#check (dist_comm _ _ : dist x y = dist y x)
#check (dist_triangle _ _ _ : dist x z ≤ dist x y + dist y z)

def ball (r : ℝ) (c : X) : Set X := { p : X | dist c p < r }

lemma ball_sub_ball' (a b : ℝ) (c : X) (h : a ≤ b) :
  ball a c ⊆ ball b c := by
  unfold ball
  simp
  intro p
  intro h'
  linarith


example (r₁ r₂ : ℝ) (x₁ x₂ c : X)
  (h : c ∈ ball r₁ x₁ ∩ ball r₂ x₂) :
  ∃ (r : ℝ), ball r c ⊆ ball r₁ x₁ ∩ ball r₂ x₂ := by
  let s₁ := r₁ - dist x₁ c
  let s₂ := r₂ - dist x₂ c
  let s := min s₁ s₂
  have hs₁ : s ≤ s₁ := min_le_left s₁ s₂
  have hs₂ : s ≤ s₂ := min_le_right s₁ s₂

  have h1 : ball s₁ c ⊆ ball r₁ x₁
  intro p
  unfold ball
  simp
  intro h'
  have k : dist c p + dist x₁ c < r₁ := lt_sub_iff_add_lt.mp h'
  have k' : dist x₁ p ≤ dist x₁ c + dist c p := dist_triangle _ _ _
  linarith

  have h2 : ball s₂ c ⊆ ball r₂ x₂
  intro p
  unfold ball
  simp
  intro h'
  have k : dist c p + dist x₂ c < r₂ := lt_sub_iff_add_lt.mp h'
  have k' : dist x₂ p ≤ dist x₂ c + dist c p := dist_triangle _ _ _
  linarith

  have hs₁' : ball s c ⊆ ball s₁ c := by
    apply ball_sub_ball'
    exact hs₁
  have h1' : ball s c ⊆ ball r₁ x₁ := Set.Subset.trans hs₁' h1
  have hs₂' : ball s c ⊆ ball s₂ c := by
    apply ball_sub_ball'
    exact hs₂
  have h2' : ball s c ⊆ ball r₂ x₂ := Set.Subset.trans hs₂' h2

  use s
  exact Set.subset_inter h1' h2'


variable [MetricSpace ℝ]

def f (x : ℝ) : ℝ := -x


example : Isometry f := by
  unfold Isometry
  intros x1 x2
  unfold f
  apply?

  refine Isometry.edist_eq ?hf x1 x2

  exact edist_mul_left 2 x1 x2

  have h := edist_add_right x1 x2 (1 : ℝ)


example (a b c d : ℝ) (h : a ≤ b) (h' : c ≤ d): (a + c ≤ b + d) := by exact add_le_add h h'

-- this is `abs_dist_sub_le`
example : |dist x z - dist y z| ≤ dist x y := by
  have h : dist x z ≤ dist x y + dist y z := dist_triangle x y z
  apply abs_sub_le_iff.mpr
  constructor
  exact sub_le_iff_le_add.mpr h

  have h : dist x y ≤ dist x z + dist z y := dist_triangle _ _ _
  have h' : - dist z x - dist y x ≤ - dist z x - dist y x := Eq.le rfl
  have h'' := add_le_add h h'
  have h''' := neg_le_neg h''
  ring_nf at h'''



--Suppose that B1 and B2 are open balls and p ∈ B1 ∩ B2 is
--a point in the intersection. Prove that there is a third open ball B3 such that
--p ∈ B3 and B3 ⊂ B1 ∩ B2. The solution to this uses the triangle inequality
--in a crucial way.
