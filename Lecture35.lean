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

#check id
#check (id : A → A)
#check (id : B → B)
#check (id : B → C)
#check @id A

example (D : Set A) : (f '' D = { b : B | ∃ a : A, a ∈ D ∧ f a = b }) := rfl

example (D : Set A) : id '' D = D := by simp only [id_eq, image_id']

example : IsOpenMap (id : A → A) := by
  unfold IsOpenMap
  intro U
  intro hU
  simp only [id_eq, image_id']
  exact hU

example : ¬ IsOpenMap (fun (x : ℝ) => (0 : ℝ)) := by
  unfold IsOpenMap
  push_neg
  use univ
  constructor
  exact isOpen_univ
  simp only [image_univ, range_const]
  exact not_isOpen_singleton 0

example (hf : IsOpenMap f) (hg : IsOpenMap g) : IsOpenMap (g ∘ f) :=
  IsOpenMap.comp hg hf

example (hf : IsOpenMap f) (hg : IsOpenMap g) : IsOpenMap (g ∘ f) :=
  fun U hU => by
    rw [image_comp]
    apply hg
    apply hf
    apply hU

variable (hAB : A ≃ₜ B)
variable (hBC : B ≃ₜ C)

#check (hAB.toFun : A → B)
#check (hAB.invFun : B → A)

example : A ≃ₜ C := Homeomorph.trans hAB hBC
example : A ≃ₜ C := ⟨
  toFun := sorry,
  ⟩

example : (ℝ ≃ₜ ℝ) := Homeomorph.neg ℝ
example : (ℝ ≃ₜ ℝ) := Homeomorph.refl ℝ
example : (A ≃ₜ A) := Homeomorph.refl A

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
