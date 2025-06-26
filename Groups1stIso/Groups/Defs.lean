import Mathlib.Tactic

namespace MyGroup

class MyGroup (G: Type _) extends Mul G, One G, Inv G where
  mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c)
  one_mul : ∀ a : G, 1 * a = a
  mul_one : ∀ a : G, a * 1 = a
  mul_left_inv : ∀ a : G, a⁻¹ * a = 1
  mul_right_inv : ∀ a : G, a * a⁻¹ = 1


class AbeGroup (G : Type _) extends MyGroup G where
  mul_comm : ∀ a b : G, a * b = b * a

structure MySubgroup (G : Type _) [MyGroup G] (H : Set G) where
  identity : 1 ∈ H
  mul_closed : ∀ a b : G, a ∈ H ∧ b ∈ H → a * b ∈ H
  inv_closed : ∀ a ∈ H, a⁻¹ ∈ H

structure NormalSubgroup (G : Type _) [MyGroup G] (H : Set G) extends MySubgroup G H where
  normal : ∀ a b : G, b ∈ H → a * b * a⁻¹ ∈ H

end MyGroup
