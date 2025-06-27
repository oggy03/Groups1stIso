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

-- Kernel of a group homomorphism is a normal subgroup
instance Myker_is_normal (f : G → H) [MyGroupHom f] :
  NormalSubgroup G (Myker f) := by sorry

-- Image of a group homomorphism is a group
instance Myim_is_group (f : G → H) [MyGroupHom f] :
  MyGroup (Myim f) := by sorry

-- The first isomorphism theorem
theorem FirstIsoTheorem (f : G → H) [MyGroupHom f] :
  ∃ φ : MyQuotientGroup (Myker_is_normal f) → Myim f,
    MyGroupHom φ ∧
    Function.Bijective φ := by sorry

end OurFirstIso
