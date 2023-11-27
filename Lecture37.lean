import Mathlib.Tactic

-- Math 4345: Lecture 37
--  _              _                    __________
-- | |    ___  ___| |_ _   _ _ __ ___  |___ /___  |
-- | |   / _ \/ __| __| | | | '__/ _ \   |_ \  / /
-- | |__|  __/ (__| |_| |_| | | |  __/  ___) |/ /
-- |_____\___|\___|\__|\__,_|_|  \___| |____//_/
--
--
-- Welcome back from Thanksgiving break!
--
-- This week we have "algebra" which for us means "group theory"

variable {G : Type*}
variable [Group G]

-- groups

example (x y z : G) : x * y * z = x * (y * z) := mul_assoc _ _ _
example (x : G) : x⁻¹ * x = 1 := mul_left_inv _
example (x : G) : x * x⁻¹ = 1 := mul_inv_self _
example (x : G) : 1 = x * x⁻¹ := (mul_inv_self _).symm

-- recall ring?  `group` is also a tactic.
example (x y : G) : y * x * (y * x) * (x * y * x)⁻¹ * y⁻¹ = 1 := by group

--
section

variable {A : Type*} [AddCommGroup A]

example (x y : A) : x + y + x + (x - y - y) = x + x + x - y := by abel

end section

-- group homomorphisms are "bundled"
section

variable {H : Type*}
variable [Group H]

example (x y : G) (f : G →* H) : f (x * y) = (f x) * (f y) := f.map_mul x y
example (x : G) (f : G →* H) : f (x⁻¹) = (f x)⁻¹ := f.map_inv x

end section
