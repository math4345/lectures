import Mathlib.Tactic
open Function
open Set

-- Math 4345: Lecture 24
--  _              _                    ____  _  _   
-- | |    ___  ___| |_ _   _ _ __ ___  |___ \| || |  
-- | |   / _ \/ __| __| | | | '__/ _ \   __) | || |_ 
-- | |__|  __/ (__| |_| |_| | | |  __/  / __/|__   _|
-- |_____\___|\___|\__|\__,_|_|  \___| |_____|  |_|  
--                                                   
-- 

-- Credit for today's lecture: Mathematics in Lean

theorem Cantor (f : α → Set α) : ¬ Surjective f := by
  intro hs
  let S := { i | i ∉ f i }
  rcases hs S with ⟨ x, hx ⟩
  have h1 : x ∉ f x := by
    intro h'
    have : x ∉ f x := by rwa [hx] at h'
    contradiction
  have h2 : x ∉ S := by
    rw [hx] at h1
    assumption
  have h3 : x ∈ S := by
    rw [mem_setOf] at h2
    push_neg at h2
    rw [hx] at h2
    assumption
  contradiction

variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) := Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun (y : β) =>
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) :
  f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f → LeftInverse (inverse f) f := by
  intro h'
  unfold LeftInverse
  intro x
  unfold inverse
  have hx : ∃ x_1, f x_1 = f x := by use x
  rw [dif_pos hx]
  have hf : f (choose hx) = f x := Classical.choose_spec hx
  exact h' hf

example : Surjective f → RightInverse (inverse f) f :=
  sorry
  