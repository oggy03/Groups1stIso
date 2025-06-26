import Mathlib.Tactic

namespace MyGroup

class Group (G : Type _) extends Mul G, One G, Inv G where
  mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c)
  one_mul : ∀ a : G, 1 * a = a
  mul_one : ∀ a : G, a * 1 = a
  mul_left_inv : ∀ a : G, a⁻¹ * a = 1
  mul_right_inv : ∀ a : G, a * a⁻¹ = 1

-- structure Group (G : Type) where
--   mul : G → G → G
--   id : G
--   inv : G → G
--   mul_assoc: ∀ (a b c : G), mul (mul a b) c = mul a (mul b c)
--   id_mul: ∀ (a : G), mul a id = a
--   mul_left_inv: ∀ (a : G), mul (inv a) a = id
--   mul_right_inv: ∀ (a : G), mul a (inv a) = id


class AbeGroup (G : Type _) extends Group G where
  mul_comm : ∀ a b : G, a * b = b * a

end MyGroup
