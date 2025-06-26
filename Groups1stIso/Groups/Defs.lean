import Mathlib.Tactic

namespace OurGroup

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
  normal : ∀ (g : G) (h : H) , g * h * g⁻¹ ∈ H

-- structure LeftCoset (G : Type _) [MyGroup G] (H : Set G) (_: MySubgroup G H) where
--   Rep : G
--   elements : Set G := {h' | ∃ h ∈ H, h' = Rep * h}

def LeftCoset  (G : Type _) [MyGroup G] (rep : G) (H : Set G) (_: MySubgroup G H) :
  Set G := { g' | ∃ h ∈ H, g' = rep * h }

def RightCoset (G : Type _) [MyGroup G] (H : Set G) (_: MySubgroup G H) (Rep : G) : Set G :=
  {h' | ∃ h ∈ H, h' = h * Rep}

-- def RightCoset (G : Type _) [MyGroup G] (H : Set G) (_: MySubgroup G H) (Rep : G) : Set G :=
--   {h * Rep | h ∈ H}

def Trivial (G : Type _) [MyGroup G] : Set G := {1}

end OurGroup

namespace OurQuotient
open OurGroup
variable {G : Type _} [MyGroup G]
variable {H : Set G} (n : NormalSubgroup G H)

def QuotientSet : Set (Set G) := { s | ∃ g : G, s = LeftCoset G g H n.toMySubgroup }

abbrev Coset := {s : Set G // s ∈ QuotientSet n}

noncomputable def QuotientMul : Coset n → Coset n → Coset n :=
  fun A B =>
    -- A and B are pairs: A.val is the set, A.property is the proof it's a coset.
    -- From A.property, we know `∃ g, A.val = LeftCoset...`. `choose` picks one such `g`.
    let gA := Classical.choose A.property
    let gB := Classical.choose B.property
    -- The resulting set is the coset of the product of the representatives.
    let C_val := LeftCoset G (gA * gB) H n.toMySubgroup
    -- We must prove this resulting set is also a valid coset.
    have C_property : C_val ∈ QuotientSet n := by use (gA * gB)
    -- The proof is that `gA * gB` is a valid representative.
    -- Return the new coset, which is the pair of the set and the proof.
    ⟨C_val, C_property⟩

end OurQuotient
