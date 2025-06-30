import Mathlib.Tactic
import Mathlib.Logic.Function.Defs
import Mathlib.Data.Set.Image
import Groups1stIso.Groups.Defs

open OurGroup

namespace OurGroupHom

variable {G H: Type _} [MyGroup G] [MyGroup H]
variable (f : G → H)

class MyGroupHom : Prop where
  hom_mul : ∀ a b : G, f (a * b) = f a * f b
  hom_id : f (1 : G) = 1
  hom_inv : ∀ a : G, f (a⁻¹) = (f a)⁻¹

class MyGroupIso (f : G → H) extends MyGroupHom f where
  bijective : Function.Bijective f

def Myker [MyGroupHom f] : Set G :=
  Set.preimage f (Trivial H)

def Myim [MyGroupHom f] : Set H :=
  Set.range f


end OurGroupHom

open OurGroupHom OurGroup OurGroupProp OurQuotient

namespace OurFirstIso

variable {G H : Type _} [MyGroup G] [MyGroup H]
variable (f : G → H) [MyGroupHom f]


-- Kernel of a group homomorphism is a subgroup
instance Myker_is_subgroup :
  MySubgroup G (Myker f) := by
  constructor
  · refine Set.mem_preimage.mpr ?_
    have : f (1 : G) = 1 := MyGroupHom.hom_id
    exact this
  · intro a b h
    obtain ⟨ha, hb⟩ := h
    refine Set.mem_preimage.mpr ?_
    have : f (a * b) = f a * f b := MyGroupHom.hom_mul a b
    rw [this, ha, hb, MyGroup.one_mul]
    rfl
  · intro a ha
    refine Set.mem_preimage.mpr ?_
    have : f (a⁻¹) = (f a)⁻¹ := MyGroupHom.hom_inv a
    rw [this, ha, OurGroupProp.one_inv (G := H)]
    rfl

-- Kernel of a group homomorphism is a normal subgroup
instance Myker_is_normal :
  NormalSubgroup G (Myker f) := by
  constructor
  · exact Myker_is_subgroup f
  · intro g h
    refine Set.mem_preimage.mpr ?_
    have : f (g * h * g⁻¹) = f g * f h * (f g)⁻¹ := by
      simp only [MyGroupHom.hom_mul, MyGroupHom.hom_inv, MyGroup.one_mul]
    rw [this]
    have : f h = 1 := by
      have h_in_ker := h.property
      simp only [Myker, Set.mem_preimage, Set.mem_singleton_iff] at h_in_ker
      exact h_in_ker
    rw [this]
    simp only [MyGroup.one_mul, MyGroup.mul_one]
    rw [MyGroup.mul_right_inv]
    rfl


-- Image of a group homomorphism is a group
instance Myim_is_group :
  MyGroup (Myim f) := by
  sorry

-- The first isomorphism theorem
theorem FirstIsoTheorem :
  ∃ φ : MyQuotientGroup (Myker_is_normal f) → Myim f,
    MyGroupIso φ := by sorry
    
end OurFirstIso
