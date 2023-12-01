import Mathlib.Tactic

-- Math 4345: Lecture 39
--  _              _                    _____ ___
-- | |    ___  ___| |_ _   _ _ __ ___  |___ // _ \
-- | |   / _ \/ __| __| | | | '__/ _ \   |_ \ (_) |
-- | |__|  __/ (__| |_| |_| | | |  __/  ___) \__, |
-- |_____\___|\___|\__|\__,_|_|  \___| |____/  /_/
--
--

variable {G : Type*}
variable [Group G]
variable (H H' : Subgroup G)

example (x y: G) (hx : x ∈ H) (hy : y ∈ H) : x * y ∈ H := H.mul_mem hx hy
example (x : G) (hx : x ∈ H) : x⁻¹ ∈ H := H.inv_mem hx

#check H ⊓ H'
#check H ⊔ H'

example (x y : G) (hx : x ∈ H) (hy : y ∈ H') : x * y ∈ Subgroup.closure ((H : Set G) ∪ (H' : Set G)) := by
  let S := (H : Set G) ∪ (H' : Set G)
  have hx' : x ∈ S := Set.mem_union_left (↑H') hx
  have hy' : y ∈ S := Set.mem_union_right (↑H) hy
  have hx'' : x ∈ Subgroup.closure S := by sorry
  have hy'' : y ∈ Subgroup.closure S := by sorry
  exact Subgroup.mul_mem (Subgroup.closure S) hx'' hy''

variable (f : G →* G)

example : Subgroup G := Subgroup.map f H
example : Subgroup G := Subgroup.comap f H

#check f.mem_ker
#check f.mem_range
