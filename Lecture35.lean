import Mathlib.Tactic
open Set

-- Math 4345: Lecture 35
--  _              _                    _________
-- | |    ___  ___| |_ _   _ _ __ ___  |___ / ___|
-- | |   / _ \/ __| __| | | | '__/ _ \   |_ \___ \
-- | |__|  __/ (__| |_| |_| | | |  __/  ___) |__) |
-- |_____\___|\___|\__|\__,_|_|  \___| |____/____/
--
--

section

variable (A B C : Type*)
variable [TopologicalSpace A]
variable [TopologicalSpace B]
variable [TopologicalSpace C]
variable (f : A → B) (g : B → C)

example (hf : IsOpenMap f) (hg : IsOpenMap g) : IsOpenMap (g ∘ f) := by sorry

variable (hAB : A ≃ₜ B)
variable (hBC : B ≃ₜ C)

example : A ≃ₜ C := by sorry

end section

variable (X : Type*)
variable [TopologicalSpace X]

example (A : Set ℝ) (h : IsOpen A) : IsOpen (A ∪ Set.Ioo 0 1) := by sorry

variable (Y : Type*)

instance : TopologicalSpace Y where
  IsOpen (h : Set Y) : Prop := (h = univ) ∨ (h = ∅)
  isOpen_univ := by sorry
  isOpen_inter := sorry
  isOpen_sUnion := sorry
