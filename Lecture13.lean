import Mathlib.Tactic

-- Math 4345: Lecture 13
--  _              _                    _ _____ 
-- | |    ___  ___| |_ _   _ _ __ ___  / |___ / 
-- | |   / _ \/ __| __| | | | '__/ _ \ | | |_ \ 
-- | |__|  __/ (__| |_| |_| | | |  __/ | |___) |
-- |_____\___|\___|\__|\__,_|_|  \___| |_|____/ 
--                                              
-- 

section

inductive list where
  | nil : list
  | cons (x : ℕ) (xs : list) : list
deriving Repr

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

def append : list → list → list 
  | nil => fun ys => ys
  | cons x xs => fun ys => cons x (append xs ys)

#eval append (cons 1 (cons 2 nil)) (cons 3 (cons 4 (cons 5 nil)))

def reverse : list → list
  | nil => nil
  | cons x xs => append (reverse xs) (cons x nil)

#eval reverse (cons 1 (cons 2 (cons 3 nil)))

theorem append_nil : ∀ (xs : list), append xs nil = xs := by
  intro xs
  induction' xs with x xs ih
  rfl
  have h : append (cons x xs) nil = cons x (append xs nil) := rfl 
  rw [h]
  rw [ih]
  
theorem nil_append : ∀ (xs : list), append nil xs = xs := by
  intro xs
  rfl

theorem reverse_nil : reverse nil = nil := by
  rfl

theorem rev_singleton : ∀ (x : ℕ), reverse (cons x nil) = cons x nil := by
  intro x
  rfl

theorem append_append : ∀ (xs : list) (ys : list) (zs : list), append xs (append ys zs) = append (append xs ys) zs := by
  intro xs
  intro ys
  intro zs
  induction' xs with x xs ih
  rw [nil_append, nil_append]
  have : ∀ (ws : list) (ws' : list), append (cons x ws') ws = cons x (append ws' ws) := by
    intro ws
    intro ws'
    rfl
  rw [this, this, this]
  rw [ih]

theorem rev_append : ∀ (xs : list) (ys : list), append (reverse xs) (reverse ys) = reverse (append ys xs) := by
  intro xs
  intro ys
  induction' ys with y ys ih
  rw [reverse_nil]
  rw [nil_append]
  rw [append_nil]
  have : reverse (cons y ys) = append (reverse ys) (cons y nil) := rfl
  rw [this]
  have : append (cons y ys) xs = cons y (append ys xs) := rfl
  rw [this]
  have : reverse (cons y (append ys xs)) = append (reverse (append ys xs)) (cons y nil) := rfl
  rw [this]
  rw [← ih]
  rw [append_append]
  
theorem rev_rev : ∀ (xs : list), reverse (reverse xs) = xs := by
  intro xs
  induction' xs with x xs ih
  rfl
  have h : reverse (cons x xs) = append (reverse xs) (cons x nil) := rfl
  rw [h]
  rw [← rev_append]
  rw [ih]
  rw [rev_singleton]
  rfl

end section

-- new tactic: calc

section

example (x y : ℝ) (h1 : x + y = 8) (h2 : x - y = 2) : x = 5 := by
  linarith

example (x y : ℝ) (h1 : x + y = 8) (h2 : x * y = 16) : x = 4 := by
  have h : (x - y)^2 = 0 :=
    calc (x - y)^2 = (x + y) ^ 2 - 4 * (x * y) := by ring
                 _ = 8 ^ 2 - 4 * 16 := by rw [h1, h2]
                 _ = 0 := by norm_num
  have h' : x - y = 0 := sq_eq_zero_iff.mp h
  linarith

example (
  x y : ℝ) (h1 : x + y = 8) (h2 : x * y = 15) : x = 3 ∨ x = 5 := by
  have h : (x - 3) * (y - 3) = 0 :=
    calc (x - 3) * (y - 3) = x * y - 3 * (x + y) + 9 := by ring
         _ = 15 - 3 * 8 + 9 := by rw [h1,h2]
         _ = 0 := by norm_num
  have h' : x - 3 = 0 ∨ y - 3 = 0 := zero_eq_mul.mp (Eq.symm h)  
  rcases h' with h'|h'
  left ; linarith
  right ; linarith

example (x y : ℝ) (h1 : x + y = 8) (h2 : x * y = 16) : x = 4 := by
  polyrith

example (x y : ℝ) : x * y ≤ ( (x + y) / 2 ) ^ 2 := by
  have h : ((x - y)/2)^2 ≥ 0 := sq_nonneg ((x - y)/2)
  exact
    calc x * y 
      ≤ x * y + ((x - y)/2)^2 := le_add_of_nonneg_right h
      _ = ((x + y)/2) ^ 2 := by ring
  
end section
