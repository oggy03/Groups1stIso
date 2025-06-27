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


--- Kernel of a group homomorphism is a subgroup
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
  -- The type `Myim f` is a subtype of H. Its elements are pairs `⟨value, proof⟩`
  -- where `value` is an element of H and `proof` is a proof that it's in the image.
  -- We will define the group structure on this subtype.

  -- 1. Define the identity element for the image
  let one_im : Myim f := {
    val := 1,
    property := by
      -- We must prove that 1 is in the image of f.
      -- Myim f is the range of f, so we need to show ∃ x:G, f x = 1.
      -- We know f(1 : G) = 1 from the homomorphism property.
      dsimp [Myim] -- simplifies Myim to Set.range
      use (1 : G)
      exact MyGroupHom.hom_id
  }

  -- 2. Define multiplication for the image
  let mul_im (a b : Myim f) : Myim f := {
    val := a.val * b.val,
    property := by
      -- We must prove that if a and b are in the image, a*b is also in the image.
      dsimp [Myim]
      -- a.property is the proof that ∃ x, f x = a.val
      -- b.property is the proof that ∃ y, f y = b.val
      obtain ⟨x, hx⟩ := a.property
      obtain ⟨y, hy⟩ := b.property
      -- We need to show ∃ z, f z = a.val * b.val
      -- The element z will be x * y.
      use (x * y)
      -- Rewrite using the proofs from above and the homomorphism property
      have h: f (x * y) = f x * f y := MyGroupHom.hom_mul x y
      rw [h, hx, hy]
  }

  -- 3. Define the inverse for the image
  let inv_im (a : Myim f) : Myim f := {
    val := (a.val)⁻¹,
    property := by
      -- We must prove that if a is in the image, a⁻¹ is also in the image.
      dsimp [Myim]
      obtain ⟨x, hx⟩ := a.property
      -- We need to show ∃ z, f z = (a.val)⁻¹
      -- The element z will be x⁻¹.
      use (x⁻¹)
      have h: f (x⁻¹) = (f x)⁻¹ := MyGroupHom.hom_inv x
      rw [h, hx]
  }

  -- Now we provide these definitions and proofs to construct the MyGroup instance.
  exact {
    one := one_im,
    mul := mul_im,
    inv := inv_im,

    -- The remaining group axioms are true because the operations are inherited
    -- from the group H. We just need to show this to Lean.
    one_mul := by
      intro a
      -- This asks to prove 1 * a = a for elements of the subtype.
      -- `Subtype.ext` says it's enough to prove it for their .val parts.
      apply Subtype.ext
      simp only [mul_im, one_im] -- Unfold the definitions we made
      exact MyGroup.one_mul a.val
    ,
    mul_one := by
      intro a
      apply Subtype.ext
      simp only [mul_im, one_im]
      exact MyGroup.mul_one a.val
    ,
    mul_assoc := by
      intros a b c
      apply Subtype.ext
      simp only [mul_im]
      exact MyGroup.mul_assoc a.val b.val c.val
    ,
    mul_left_inv := by
      intro a
      apply Subtype.ext
      simp only [mul_im, inv_im, one_im]
      exact MyGroup.mul_left_inv a.val
    ,
    mul_right_inv := by
      intro a
      apply Subtype.ext
      simp only [mul_im, inv_im, one_im]
      exact MyGroup.mul_right_inv a.val
  }

-- The first isomorphism theorem
theorem FirstIsoTheorem :
  ∃ φ : MyQuotientGroup (Myker_is_normal f) → Myim f,
    MyGroupIso φ := by sorry

end OurFirstIso
