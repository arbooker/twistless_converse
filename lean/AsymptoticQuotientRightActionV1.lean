module

public import AsymptoticOvergroupIsometryV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticNestedQuotients

variable {G : Type*} [Group G]

theorem classOf_eq_iff (H : Subgroup G) (g h : G) :
    classOf H g=classOf H h ↔ g*h⁻¹∈H := by
  constructor
  · intro he
    have hm := QuotientGroup.rightRel_apply.mp (Quotient.exact he)
    simpa only [mul_inv_rev,inv_inv] using H.inv_mem hm
  · intro hm
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    simpa only [mul_inv_rev,inv_inv] using H.inv_mem hm

/-- Right multiplication acts on the left-coset counting coordinates. -/
def rightMulEquiv (H : Subgroup G) (a : G) : Classes H ≃ Classes H where
  toFun := Quotient.map (fun g => g*a) (by
    intro g h he
    apply QuotientGroup.rightRel_apply.mpr
    have hh := QuotientGroup.rightRel_apply.mp he
    simpa only [mul_inv_rev,mul_assoc,mul_inv_cancel_left] using hh)
  invFun := Quotient.map (fun g => g*a⁻¹) (by
    intro g h he
    apply QuotientGroup.rightRel_apply.mpr
    have hh := QuotientGroup.rightRel_apply.mp he
    simpa only [mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel_left] using hh)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h g =>
      change classOf H ((g*a)*a⁻¹)=classOf H g
      rw [mul_inv_cancel_right]
  right_inv q := by
    induction q using Quotient.inductionOn with
    | h g =>
      change classOf H ((g*a⁻¹)*a)=classOf H g
      rw [inv_mul_cancel_right]

theorem rightMulEquiv_classOf (H : Subgroup G) (a g : G) :
    rightMulEquiv H a (classOf H g)=classOf H (g*a) := rfl

theorem forget_rightMul {H J : Subgroup G} (h : H≤J) (a : G) (q : Classes H) :
    forget h (rightMulEquiv H a q)=rightMulEquiv J a (forget h q) := by
  induction q using Quotient.inductionOn with
  | h g => rfl

#print axioms classOf_eq_iff
#print axioms rightMulEquiv_classOf
#print axioms forget_rightMul

end AsymptoticNestedQuotients
