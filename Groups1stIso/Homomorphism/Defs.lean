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
