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

-- def s3 := Equiv.Perm (Fin 3)
-- example : Group s3 := by infer_instance

-- groups

example (x y z : G) : x * y * z = x * (y * z) := mul_assoc x y z
example (x : G) : x⁻¹ * x = 1 := mul_left_inv x
example (x : G) : x * x⁻¹ = 1 := mul_inv_self _
example (x : G) : 1 = x * x⁻¹ := (mul_inv_self _).symm

-- recall ring?  `group` is also a tactic.
example (x y : G) : y * x * (y * x) * (x * y * x)⁻¹ * y⁻¹ = 1 := by
  group

--
section

variable {H : Type*}
variable [CommGroup H]

example (x y : H) : x * y = y * x := mul_comm _ _

variable {A : Type*}
variable [AddCommGroup A]

example (x y : A) : x + y = y + x := add_comm _ _
example (x y : A) : x + y = y + x := by abel
example (x y : A) : x + y + x + (x - y - y) = x + x - y + x := by
  abel

end section

-- group homomorphisms are "bundled"
section

variable {H : Type*}
variable [Group H]
variable (f : G →* H)

variable (g : G)
#check (f.toFun g : H)

example (x y : G) : f (x * y) = (f x) * (f y) := f.map_mul x y

example (x : G) : f (x⁻¹) = (f x)⁻¹ := f.map_inv x

lemma fxi_fx (x : G) : (f (x⁻¹)) * (f x) = 1 := by
  rw [← map_mul]
  group
  exact f.map_one

end section

section

variable {H : Type*}
variable [Group H]
variable (f : G →* H)

variable (g : G)
variable (hg : g * g * g = 1)

lemma fg : ∃ (h : H), h * h * h = 1 := by
  use f g
  rw [← f.map_mul]
  rw [← f.map_mul]
  rw [hg]
  rw [map_one]

end section

section

variable {H : Type*}
variable [Group H]

def f : G →* H := {
  toFun := fun (_ : G) => (1 : H),
  map_one' := by simp,
  map_mul' := by simp
}

end section

section

variable (S : Set G)
variable (H : Subgroup G) -- think about Set G

example (x y : G) (hx : x ∈ H) (hy : y ∈ H) : x * y ∈ H :=
H.mul_mem hx hy

end section

example {G : Type*} [Group G] (H : Subgroup G) {x : G} (hx : x ∈ H) :
  x⁻¹ ∈ H :=
H.inv_mem hx

example {G H : Type*} [Group G] [Group H] (f : G → H) (h : ∀ x y, f (x * y) = f x * f y) :
  G →* H :=
MonoidHom.mk' f h

example {G : Type*} [Group G] (H H' : Subgroup G) :
  ((H ⊓ H' : Subgroup G) : Set G) = (H : Set G) ∩ (H' : Set G) := rfl


example {G : Type*} [Group G] (H H' : Subgroup G) :
    ((H ⊔ H' : Subgroup G) : Set G) = Subgroup.closure ((H : Set G) ∪ (H' : Set G)) := by
  rw [Subgroup.sup_eq_closure]


  example {G H : Type*} [Group G] [Group H] (G' : Subgroup G) (f : G →* H) : Subgroup H :=
  Subgroup.map f G'

example {G H : Type*} [Group G] [Group H] (H' : Subgroup H) (f : G →* H) : Subgroup G :=
  Subgroup.comap f H'

#check Subgroup.mem_map
#check Subgroup.mem_comap

example {G H : Type*} [Group G] [Group H] (f : G →* H) (g : G) :
    g ∈ MonoidHom.ker f ↔ f g = 1 :=
  f.mem_ker

example {G H : Type*} [Group G] [Group H] (f : G →* H) (h : H) :
    h ∈ MonoidHom.range f ↔ ∃ g : G, f g = h :=
  f.mem_range

section exercises
variable {G H : Type*} [Group G] [Group H]

open Subgroup

example (φ : G →* H) (S T : Subgroup H) (hST : S ≤ T) : comap φ S ≤ comap φ T :=by
  sorry

example (φ : G →* H) (S T : Subgroup G) (hST : S ≤ T) : map φ S ≤ map φ T :=by
  sorry

variable {K : Type*} [Group K]

-- Remember you can use the `ext` tactic to prove an equality of subgroups.
example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) :
  comap (ψ.comp φ) U = comap φ (comap ψ U) := by
  sorry

-- Pushing a subgroup along one homomorphism and then another is equal to
--  pushing it forward along the composite of the homomorphisms.
example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) :
  map (ψ.comp φ) S = map ψ (S.map φ) := by
  sorry
