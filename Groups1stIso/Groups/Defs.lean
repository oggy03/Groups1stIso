import Mathlib.Tactic

namespace MyGroup

variable {G : Type _}

class MyGroup extends Mul G, One G, Inv G where
  mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c)
  one_mul : ∀ a : G, 1 * a = a
  mul_one : ∀ a : G, a * 1 = a
  mul_left_inv : ∀ a : G, a⁻¹ * a = 1
  mul_right_inv : ∀ a : G, a * a⁻¹ = 1


class AbeGroup extends MyGroup G where
  mul_comm : ∀ a b : G, a * b = b * a

structure MySubgroup [MyGroup G] (H: set G) where
  identity : 1 ∈ H
  mul_closed : ∀ a b : H, a * b ∈ G
  inv_closed : ∀ a : H, a⁻¹ ∈ G

structure NormalSubgroup [MyGroup G] (H: set G) extends Subgroup H where
  normal : ∀ a : G, ∀ H : G, a * b * a⁻¹ ∈ G

end MyGroup
