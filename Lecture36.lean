import Mathlib.Tactic

-- Math 4345: Lecture 36
--  _              _                    _____  __
-- | |    ___  ___| |_ _   _ _ __ ___  |___ / / /_
-- | |   / _ \/ __| __| | | | '__/ _ \   |_ \| '_ \
-- | |__|  __/ (__| |_| |_| | | |  __/  ___) | (_) |
-- |_____\___|\___|\__|\__,_|_|  \___| |____/ \___/
--
--

-- We only meet Monday this week because of Thanksgiving.

-- There is no new homework assignment this week -- use this time to
-- catch up if you are behind.

-- The topic is "algebra" which is setting us up for success next
-- week, when our topic is "group theory."

-- To focus our discussion today, we'll work with monoids.

-- "recall" the definition of monoid:
-- A monoid is a semigroup with an identity element.

-- a magma is a set with a binary operation
-- a semigroup is a magma with an _associative_ operation
-- a monoid is a semigroup with an identity element

-- ℤ/2ℤ := { 0, 1 }

-- any group is a monoid

-- "symm" will take an equality and "reverse" it
section
variable {α : Type*}
variable (x y : α)
variable (h : x = y)
#check (h.symm : y = x)
end section

-- ---- ---- ---- ---- ---- ---- ---- ---- ---- ---- ---- --

section
variable {M : Type*} [Monoid M]

#check Monoid ℕ

example (a b c : M) : (a*b)*c = a*(b*c) := mul_assoc a b c
example (a b c : M) : a*(b*c) = (a*b)*c := (mul_assoc a b c).symm

example (m : M) : 1*m = m := one_mul m
example (m : M) : m*1 = m := mul_one m
example (m : M) : m ^ 3 = m * (m * m) := pow_three m
example (m : M) : m ^ 3 = (m * m) * m := pow_three' m
example (m : M) : m ^ 2 = m * m := pow_two m

example (a b c d : M) : (a*b)*(c*d) = a*(b*c)*d := by
  rw [mul_assoc, mul_assoc, mul_assoc]

-- If an element acts like the identity,
-- it is equal to the identity.
example (e : M) (h : ∀ (m : M), e * m = m) : e = 1 := by
  specialize h 1
  rwa [mul_one] at h

end section

-- ---- ---- ---- ---- ---- ---- ---- ---- ---- ---- ---- --

section

variable {M : Type*} [Monoid M]
variable {N : Type*} [Monoid N]
variable (f : M →* N)
variable (g : N →* M)

#check f
#check f.toFun

example (x y : M) : f (x * y) = (f x) * (f y) := f.map_mul x y

example (x y : M) : g (f (x * y)) = (g (f x)) * (g (f y)) := by
  rw [← g.map_mul]
  rw [← f.map_mul]

example (x y : M) : g (f $ x * y) = (g $ f x) * (g $ f y) := by
  rw [← g.map_mul]
  rw [← f.map_mul]

variable (hfg : f ∘ g = id)
variable (hgf : g ∘ f = id)

example : M ≃ N := by exact {
    toFun := f,
    invFun := g,
    left_inv := congrFun hgf,
    right_inv := congrFun hfg,
  }

example : M ≃* N := by exact {
    toFun := f,
    invFun := g,
    left_inv := congrFun hgf,
    right_inv := congrFun hfg,
    map_mul' := by apply f.map_mul
  }

end section

-- ---- ---- ---- ---- ---- ---- ---- ---- ---- ---- ---- --

section
-- M is a monoid
variable {M : Type*} [Monoid M]

def left_inverses  (m : M) := { x : M | x * m = 1 }
def right_inverses (m : M) := { x : M | m * x = 1 }

-- if an element m ∈ M is left invertible and right inverible,
-- then these inverses are the same.
example (m : M) (xl : M) (xr : M)
 (hl : xl ∈ left_inverses m)
 (hr : xr ∈ right_inverses m) : xl = xr := by
   unfold left_inverses at hl
   unfold right_inverses at hr
   simp at *
   have : (xl * m) * xr = 1 * xr := by congr
   simp at this
   rw [mul_assoc, hr] at this
   simp at this
   assumption

end section

-- ---- ---- ---- ---- ---- ---- ---- ---- ---- ---- ---- --

section
-- M is a monoid; is it possible for an element to have distinct inverses?
end section
