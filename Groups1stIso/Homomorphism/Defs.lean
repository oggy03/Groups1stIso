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


-- Kernel of a group homomorphism is a normal subgroup
instance Myker_is_normal :
  NormalSubgroup G (Myker f) := by
  constructor
  · refine { identity := ?_, mul_closed := ?_, inv_closed := ?_ }
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
      rw [this]
      rw [ha]
      
      sorry
  · sorry

-- Image of a group homomorphism is a group
instance Myim_is_group :
  MyGroup (Myim f) := by sorry

-- The first isomorphism theorem
theorem FirstIsoTheorem :
  ∃ φ : MyQuotientGroup (Myker_is_normal f) → Myim f,
    MyGroupIso φ := by sorry

end OurFirstIso
