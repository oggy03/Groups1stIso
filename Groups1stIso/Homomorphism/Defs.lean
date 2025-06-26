import Mathlib.Tactic
import Groups1stIso.Groups.Defs
import Mathlib.Logic.Function.Defs

open OurGroup

namespace OurGroupHom

variable {G H: Type _} [MyGroup G] [MyGroup H]
variable (f : G → H)

class MyGroupHom : Prop where
  hom_mul : ∀ a b : G, f (a * b) = f a * f b

class MyGroupIso (f : G → H) extends MyGroupHom f where
  bijective : Function.Bijective f

def Myker [MyGroupHom f] : Set G :=
  { g : G | f g = 1 }

def Myim [MyGroupHom f] : Set H :=
  { h : H | ∃ (g : G), f g = h }

end OurGroupHom

open OurGroupHom
variable {G H : Type _} [MyGroup G] [MyGroup H]
variable (f : G → H) [MyGroupHom f]

lemma GroupHompreId : f 1 = 1 := by
  sorry
