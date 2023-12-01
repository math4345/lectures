import Mathlib.Tactic

-- Math 4345: Lecture 38
--  _              _                    _____  ___
-- | |    ___  ___| |_ _   _ _ __ ___  |___ / ( _ )
-- | |   / _ \/ __| __| | | | '__/ _ \   |_ \ / _ \
-- | |__|  __/ (__| |_| |_| | | |  __/  ___) | (_) |
-- |_____\___|\___|\__|\__,_|_|  \___| |____/ \___/
--
--

-- A "new" tactic: decide

inductive Animal
| Cat
| Dog
deriving Repr

open Animal

instance : Mul Animal := {
  mul := fun
          | Cat => fun
                    | Cat => Cat
                    | Dog => Cat
          | Dog => fun
                    | Cat => Cat
                    | Dog => Dog
}

instance : Inv Animal := {
  inv := fun
          | Dog => Cat
          | Cat => Cat
}

instance : Semigroup Animal := {
  mul_assoc := by
    intros a b c
    induction a
    induction b
    induction c
    <;> rfl
    induction c
    rfl
    rfl
    induction b
    induction c
    rfl
    rfl
    induction c
    rfl
    rfl
    -- ugh!
}

#eval Dog⁻¹
#eval Cat⁻¹

#eval Dog * Cat
#eval 3 * 2

#check True
#check true

#eval true * true
#eval (1 : Bool)

#eval (xor true (not true)) == false

instance : Group Bool := {
  mul := xor
  mul_assoc := by decide
  one := false
  one_mul := by
    intro a
    induction a <;> rfl
  mul_one := by decide
  inv := id
  mul_left_inv := by decide
}

#eval true * false
#eval false * true
#eval false * false
#eval true * true

#eval true * true
#eval (1 : Bool)

lemma two_two : 2 + 2 ≠ 5 := by linarith
lemma two_two' : 2 + 2 ≠ 5 := by decide
#print two_two
#print two_two'

example : (x : Bool) → (y : Bool) → ((not x) && (not y) ↔ not (x || y)) := by
  decide

example : Group (Bool × Bool) := by infer_instance

#eval (true,true) * (false,true)

example : Fintype.card Bool = 2 := by rfl

inductive Amount
| None
| Some
| Lots
deriving BEq, Fintype

open Amount

theorem pairwise_triple {a b c : α} : List.Pairwise R [a, b, c] ↔ (R a b ∧ R a c) ∧ R b c := by simp

instance : Fintype Amount := {
  elems := { val := [ None, Some, Lots ],
             nodup := by
                         refine Iff.mpr Multiset.coe_nodup ?_
                         unfold List.Nodup
                         rw [pairwise_triple]
                         simp
           },
  complete := by
    intro x
    simp
    induction x
    <;> tauto
}

example : Fintype.card Amount = 2 := by rfl

instance : Finite Amount := by infer_instance

def Amount.decEq (a b : Amount) : Decidable (Eq a b) :=
   match a, b with
   | None, None => isTrue rfl
   | Some, Some  => isTrue rfl
   | Lots, Lots => isTrue rfl
   | None, Some  => isFalse (fun h => Amount.noConfusion h)
   | None, Lots  => isFalse (fun h => Amount.noConfusion h)
   | Some, None  => isFalse (fun h => Amount.noConfusion h)
   | Some, Lots  => isFalse (fun h => Amount.noConfusion h)
   | Lots, None  => isFalse (fun h => Amount.noConfusion h)
   | Lots, Some  => isFalse (fun h => Amount.noConfusion h)

instance : DecidableEq Amount := Amount.decEq

instance : Group Amount := {
  mul := fun
    | None => fun y => y
    | Some => fun
                | None => Some
                | Some => Lots
                | Lots => None
    | Lots => fun
                | None => Lots
                | Some => None
                | Lots => Some
  mul_assoc := by decide,
  one := None,
  one_mul := by decide,
  mul_one := by decide,
  inv := fun
          | None => None
          | Some => Lots
          | Lots => Some,
  mul_left_inv := by decide
}

variable (f : Bool →* Amount)

abbrev G : Subgroup Amount :=
  Subgroup.map f (⊤ : Subgroup Bool)

lemma t : (⊥ : Subgroup Amount) = G := by
