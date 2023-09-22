import Mathlib.Tactic

-- Math 4345: Lecture 12
--  _              _                    _ ____  
-- | |    ___  ___| |_ _   _ _ __ ___  / |___ \ 
-- | |   / _ \/ __| __| | | | '__/ _ \ | | __) |
-- | |__|  __/ (__| |_| |_| | | |  __/ | |/ __/ 
-- |_____\___|\___|\__|\__,_|_|  \___| |_|_____|
--                                              
-- 

section

variable (P Q R : Prop)

example : P → (P ∨ Q) := fun h => Or.inl h

example : Q → (P ∨ Q) := fun h => Or.inr h

example : P → (P ∨ Q) := by
  intro h
  left
  exact h

example : Q → (P ∨ Q) := by
  intro h
  right
  exact h

-- this is the "left injection" from P to P ∨ Q
example : P → (P ∨ Q) := Or.inl

-- this is the "right injection" from Q to P ∨ Q
example : Q → (P ∨ Q) := Or.inr

example : (P ∨ Q) → (P ∨ Q) := fun h => h

-- here is a tactics-mode proof
example : (P ∨ Q) → (Q ∨ P) := by
  intro h
  rcases h with hp|hq
  exact Or.inr hp
  exact Or.inl hq

example : (P ∨ P) → P := by
  intro h
  rcases h with h1|h2
  exact h1
  exact h2

example : (P ∨ P) → P := fun
  | Or.inl h => h
  | Or.inr h => h

-- give a term-mode proof of this example from above
example : (P ∨ Q) → (Q ∨ P) := fun
  | Or.inl hp => Or.inr hp
  | Or.inr hq => Or.inl hq

-- give a term-mode proof of this example from above
example : (P ∨ Q) → (Q ∨ P) := fun
  | Or.inl hp => Or.inr hp
  | Or.inr hq => Or.inl hq

-- mix them!
lemma orcom : (P ∨ Q) → (Q ∨ P) := fun
  | Or.inl hp => Or.inr (by assumption)
  | Or.inr hq => by left
                    assumption 

example : (P ∨ Q) → (Q ∨ P) := Or.comm.mp

end section

section

example : ¬ (P ∧ ¬ P) := by
  intro h
  rcases h with ⟨ hp, np ⟩
  exact np hp

example : ¬ (P ∧ ¬ P) :=
  fun ⟨ hp, np ⟩ => np hp

example : ¬ (P ∧ ¬ P)
  | ⟨ hp, np ⟩ => np hp

example : ¬ (P ∧ ¬ P) := and_not_self

example : P → ¬ (P → ¬ P) := by
  intro hp
  intro h
  apply h
  exact hp
  exact hp

example : (¬ P) → (P → ¬ P) := by
  intro hp
  intro _
  exact hp

example : (¬ P) → (¬ ¬ (P → ¬ P)) := by
  intro hp
  have h : (P → ¬ P)
  intro _
  exact hp
  intro k
  exact k h

end section

-- new tactic: calc

section

example (x y : ℝ) (h1 : x + y = 8) (h2 : x * y = 16) : x = 4 := by
  have h : (x - y)^2 = 0 :=
    calc (x - y)^2 = (x + y) ^ 2 - 4 * (x * y) := by ring
                 _ = 8 ^ 2 - 4 * 16 := by rw [h1, h2]
                 _ = 0 := by norm_num
  have h' : x - y = 0 := Iff.mp sq_eq_zero_iff h
  linarith

example (x y : ℝ) : x * y ≤ ( (x + y) / 2 ) ^ 2 := by
  have h : ((x - y)/2)^2 ≥ 0 := sq_nonneg ((x - y)/2)
  exact
    calc x * y 
      ≤ x * y + ((x - y)/2)^2 := le_add_of_nonneg_right h
      _ = ((x + y)/2) ^ 2 := by ring

end section

-- Let's try a bit more "programming" in Lean

section

inductive list where
  | nil : list
  | cons (x : ℕ) (xs : list) : list

open list

#check nil

#check cons 5 (cons 3 nil)

def len : list → ℕ 
  | nil => 0
  | cons _ xs => 1 + len xs

#eval len nil

#eval len (cons 17 nil)

#eval len (cons 5 (cons 3 nil))

#eval len (cons 5 (cons 5 (cons 3 nil)))

end section

