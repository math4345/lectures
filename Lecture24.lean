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

-- Monday's lecture will be asynchronous

-- Credit for today's lecture: Mathematics in Lean

theorem Cantor (f : α → Set α) : ¬ Surjective f := by  
  -- the proof is via "diagonalization"
  let S : Set α := { i : α | i ∉ f i }
 
  -- the idea is that if f were surjective...
  intro hs
  -- there would be an x so that f x = S
  rcases hs S with ⟨ x, hx ⟩

  -- either x ∈ S or x ∉ S
  -- if x ∈ S, then x not in f x = S
  -- if x ∉ S, then x ∈ f x = S
  have h2 : x ∉ S := by
    have h1 : x ∉ f x := by
      intro h'
      have : x ∉ f x := by rwa [hx] at h'
      contradiction
    rwa [hx] at h1

  have h3 : x ∈ S := by
    rw [mem_setOf, hx] at h2
    push_neg at h2
    assumption

  contradiction

#check ({ 3 } : Set ℕ)
#check (singleton 3 : Set ℕ)

example : ∃ (f : α → Set α), Injective f := by
  use (fun x => singleton x)
  intro x₁ x₂ h
  simp only [singleton_eq_singleton_iff] at h 
  assumption

--

variable {α β : Type*} [Inhabited α]
#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) := Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun (y : β) =>
  if h : ∃ x, f x = y then choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) :
  f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact choose_spec h

example (f : α → β) (hi : Injective f) : LeftInverse (inverse f) f := by
  unfold LeftInverse
  intro x
  have k : f (inverse f (f x)) = f x := by
    apply inverse_spec
    use x
  unfold Injective at hi
  exact hi k
  
example (f : α → β) (hs : Surjective f) : RightInverse (inverse f) f := by
  intro x
  exact inverse_spec _ (hs x)

example (f : α → β) (hs : Surjective f) : RightInverse (inverse f) f := 
  fun x => inverse_spec _ (hs x)
  