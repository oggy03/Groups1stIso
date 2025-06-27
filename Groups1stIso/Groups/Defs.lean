import Mathlib.Tactic
namespace OurGroup

class MyGroup (G: Type _) extends Mul G, One G, Inv G where
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
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

@[simp]
def LeftCoset  (G : Type _) [MyGroup G] (Rep : G) (H : Set G) (_: MySubgroup G H) :
  Set G := { g' | ∃ h ∈ H, g' = Rep * h }

@[simp]
def RightCoset (G : Type _) [MyGroup G] (H : Set G) (_: MySubgroup G H) (Rep : G) : Set G :=
  {h' | ∃ h ∈ H, h' = h * Rep}

@[simp]
def Trivial (G : Type _) [MyGroup G] : Set G := {1}

end OurGroup
namespace OurGroupProp

open OurGroup
variable (G : Type _) [MyGroup G]

@[simp]
lemma mul_left_cancel (a b c : G) (h : a * b = a * c) : b = c := by
  rw [← MyGroup.one_mul b]
  rw [← MyGroup.mul_left_inv a]
  rw [MyGroup.mul_assoc]
  rw [h]
  rw [← MyGroup.mul_assoc]
  rw [MyGroup.mul_left_inv]
  rw [MyGroup.one_mul]

@[simp]
lemma mul_eq_of_eq_inv_mul {a b c : G} (h : b = a⁻¹ * c) : a * b = c := by
  rw [h]
  rw [← MyGroup.mul_assoc]
  rw [MyGroup.mul_right_inv]
  rw [MyGroup.one_mul]

@[simp]
lemma eq_mul_inv_of_mul_eq {a b c: G} (h : a * b = c) : a = c * b⁻¹ := by
  rw [← h]
  rw [MyGroup.mul_assoc]
  rw [MyGroup.mul_right_inv]
  rw [MyGroup.mul_one]

@[simp]
lemma eq_inv_mul_of_mul_eq {a b c : G} (h : b * a = c) : a = b⁻¹ * c := by
  rw [← h]
  rw [← MyGroup.mul_assoc]
  rw [MyGroup.mul_left_inv]
  rw [MyGroup.one_mul]

@[simp]
lemma mul_left_eq_self (a b : G) : a * b = b ↔ a = 1 := by
  constructor
  · intro h
    have h1 := eq_mul_inv_of_mul_eq (G := G) h
    rw [MyGroup.mul_right_inv] at h1
    exact h1
  · intro h
    rw [h]
    rw [MyGroup.one_mul]

@[simp]
lemma eq_inv_of_mul_eq_one {a b : G} (h : a * b = 1) : a = b⁻¹ := by
  rw [← MyGroup.one_mul b⁻¹]
  apply eq_mul_inv_of_mul_eq (G := G) h

@[simp]
lemma inv_inv (a : G) : a ⁻¹ ⁻¹ = a := by
  symm
  apply eq_inv_of_mul_eq_one
  exact MyGroup.mul_right_inv a

@[simp]
lemma inv_eq_of_mul_eq_one {a b : G} (h : a * b = 1) : a⁻¹ = b := by
  replace h := eq_mul_inv_of_mul_eq (G := G) h
  rw [MyGroup.one_mul] at h
  rw [h]
  rw [inv_inv]

@[simp]
lemma unique_id {e : G} (h : ∀ x : G, e * x = x) : e = 1 := by
  have h1 : e = e * 1 := by rw [MyGroup.mul_one]
  rw [h1]
  apply h 1

@[simp]
lemma unique_inv {a b : G} (h : a * b = 1) : b = a⁻¹ := by
  apply mul_left_cancel
  rw [h, MyGroup.mul_right_inv a]

lemma mul_right_cancel {a b c : G} (h : b * a = c * a) : b = c := by
  calc b = b * 1 := by rw [MyGroup.mul_one]
       _ = b * (a * a⁻¹) := by rw [MyGroup.mul_right_inv]
       _ = b * a * a⁻¹ := by rw [MyGroup.mul_assoc]
       _ = c * a * a⁻¹  := by rw [h]
       _ = c * (a * a⁻¹) := by rw [MyGroup.mul_assoc]
       _ = c * 1 := by rw [MyGroup.mul_right_inv]
       _ = c := by rw [MyGroup.mul_one]

@[simp]
lemma mul_left_cancel_iff (a x y : G) : a * x = a * y ↔ x = y := by
  constructor
  · intro h
    apply mul_left_cancel
    exact h
  · intro h
    rw [h]

@[simp]
lemma mul_right_cancel_iff (a x y : G) : x * a = y * a ↔ x = y := by
  constructor
  · intro h
    apply mul_right_cancel
    exact h
  · intro h
    rw [h]

@[simp]
lemma inv_mul (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  apply mul_left_cancel
  rw [MyGroup.mul_right_inv]
  rw [MyGroup.mul_assoc]
  rw [← MyGroup.mul_assoc b]
  rw [MyGroup.mul_right_inv]
  rw [MyGroup.one_mul]
  rw [MyGroup.mul_right_inv]

lemma one_inv : (1 : G)⁻¹ = 1 := by
  apply mul_left_cancel
  rw [MyGroup.mul_right_inv]
  rw [MyGroup.one_mul]

@[simp]
theorem inv_eq (a b : G): a⁻¹ = b ↔ b⁻¹ = a := by
  constructor
  · rintro rfl
    rw [inv_inv]
  · intro h
    rw [← h]
    rw [inv_inv]

end OurGroupProp

namespace OurQuotient
open OurGroup OurGroupProp
variable {G : Type _} [MyGroup G]
variable {H : Set G} (n : NormalSubgroup G H)

@[simp]
def NormEquiv (_ : NormalSubgroup G H) (a b : G) : Prop := a * b⁻¹ ∈ H

instance NormEquiv_is_equiv : Equivalence (NormEquiv n) where
  refl := by
        intro x
        simp only [NormEquiv]
        have h1 : x * x⁻¹ = 1 := MyGroup.mul_right_inv x
        have h2 : 1 ∈ H := n.identity
        exact Set.mem_of_eq_of_mem h1 h2
  symm := by
      intro x y h
      simp only [NormEquiv] at *
      have h_inv : (x * y⁻¹)⁻¹ ∈ H := n.inv_closed _ h
      rw [inv_mul, inv_inv] at h_inv
      exact h_inv
  trans := by
      intro x y z hxy hyz
      simp only [NormEquiv] at *
      have h_mul : (x * y⁻¹) * (y * z⁻¹) ∈ H := n.mul_closed _ _ ⟨hxy, hyz⟩
      have h_calc : (x * y⁻¹) * (y * z⁻¹) = x * z⁻¹ := by
        calc (x * y⁻¹) * (y * z⁻¹)
          _ = x * (y⁻¹ * (y * z⁻¹)) := by rw [MyGroup.mul_assoc]
          _ = x * ((y⁻¹ * y) * z⁻¹) := by rw [← MyGroup.mul_assoc y⁻¹]
          _ = x * (1 * z⁻¹)         := by rw [MyGroup.mul_left_inv]
          _ = x * z⁻¹               := by rw [MyGroup.one_mul]
      rw [h_calc] at h_mul
      exact h_mul

def MyGroupSetoid : Setoid G where
  r := NormEquiv n
  iseqv := NormEquiv_is_equiv n

def MyQuotientGroup : Type _ := Quotient (MyGroupSetoid n)

lemma NormEquiv_mul
    {a₁ a₂ b₁ b₂ : G}
    (ha : NormEquiv n a₁ a₂) (hb : NormEquiv n b₁ b₂)
    : NormEquiv n (a₁ * b₁) (a₂ * b₂) := by
  dsimp [NormEquiv] at *
  have : (a₁ * b₁) * (a₂ * b₂)⁻¹ =
         (a₁ * a₂⁻¹) * (b₁ * b₂⁻¹) := by sorry
  have h₁ : a₁ * a₂⁻¹ ∈ H := ha
  have h₂ : b₁ * b₂⁻¹ ∈ H := hb
  have : (a₁ * b₁) * (a₂ * b₂)⁻¹ ∈ H := by sorry
  exact this

lemma NormEquiv_inv {a b : G} (h : NormEquiv n a b)
  : NormEquiv n a⁻¹ b⁻¹ := by
  dsimp [NormEquiv] at *
  refine MySubgroup.mul_closed ?_ a⁻¹ b⁻¹⁻¹ ?_
  · exact n.toMySubgroup
  · constructor
    · sorry
    · sorry

def MulQuot : MyQuotientGroup n → MyQuotientGroup n → MyQuotientGroup n :=
  Quotient.map₂ (fun a b ↦ a * b)
    (by
      intro a₁ a₂ ha b₁ b₂ hb
      exact NormEquiv_mul n ha hb)

def InvQuot : MyQuotientGroup n → MyQuotientGroup n :=
  Quotient.map (fun a ↦ a⁻¹)
    (by
      intro a b h
      exact NormEquiv_inv n h)

instance MyQuotientGroup_is_group (n : NormalSubgroup G H) : MyGroup (MyQuotientGroup n) where
  mul := MulQuot n
  one := ⟦1⟧
  inv := InvQuot n
  mul_assoc := by
              intro G H K
              refine Quotient.inductionOn₃ G H K (fun g h k ↦ ?_)
              apply Quotient.sound
              dsimp [NormEquiv]
              have h_eq : g * h * k = g * (h * k) := by rw [MyGroup.mul_assoc]
              have : ((g * h) * k) * (g * (h * k))⁻¹ = 1 := by rw [h_eq, MyGroup.mul_right_inv]
              exact Quotient.exact (congrArg (Quotient.mk (MyGroupSetoid n)) h_eq)
  one_mul := by
          intro a
          refine Quotient.inductionOn a (fun g ↦ ?_)
          apply Quotient.sound
          dsimp [NormEquiv]
          have h_eq : 1 * g = g := by rw [MyGroup.one_mul]
          have : 1 * g * (1 * g)⁻¹ = 1 := by rw [h_eq, MyGroup.mul_right_inv]
          exact Quotient.exact (congrArg (Quotient.mk (MyGroupSetoid n)) h_eq)
  mul_one := by
          intro a
          refine Quotient.inductionOn a (fun g ↦ ?_)
          apply Quotient.sound
          dsimp [NormEquiv]
          have h_eq : g * 1 = g := by rw [MyGroup.mul_one]
          have : g * 1 * (g * 1)⁻¹ = 1 := by rw [h_eq, MyGroup.mul_right_inv]
          exact Quotient.exact (congrArg (Quotient.mk (MyGroupSetoid n)) h_eq)
  mul_left_inv := by
          intro a
          refine Quotient.inductionOn a (fun g ↦ ?_)
          apply Quotient.sound
          dsimp [NormEquiv]
          have h_eq : g⁻¹ * g = 1 := by rw [MyGroup.mul_left_inv]
          have : g⁻¹ * g * (g⁻¹ * g)⁻¹ = 1 := by rw [h_eq, MyGroup.mul_right_inv]
          exact Quotient.exact (congrArg (Quotient.mk (MyGroupSetoid n)) h_eq)
  mul_right_inv := by
          intro a
          refine Quotient.inductionOn a (fun g ↦ ?_)
          apply Quotient.sound
          dsimp [NormEquiv]
          have h_eq : g * g⁻¹ = 1 := by rw [MyGroup.mul_right_inv]
          have : g * g⁻¹ * (g * g⁻¹)⁻¹ = 1 := by rw [h_eq, MyGroup.mul_right_inv]
          exact Quotient.exact (congrArg (Quotient.mk (MyGroupSetoid n)) h_eq)

end OurQuotient
