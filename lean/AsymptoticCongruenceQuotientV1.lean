module

public import AsymptoticNormalizedCongruenceWeightV1
public import AsymptoticFiberIsometryV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticCongruenceQuotient

open UpperHalfPlane AsymptoticCongruenceStrip AsymptoticCongruenceWeight
open scoped lp

/-- Congruence classes of labels on one rational orbit. -/
noncomputable abbrev Classes (N : ℕ) :=
  Quotient (QuotientGroup.rightRel (gamma N))

noncomputable def classOf (N : ℕ) (g : AsymptoticRationalGroup.Group) : Classes N :=
  Quotient.mk _ g

theorem classOf_mul (N : ℕ) (h : gamma N) (g : AsymptoticRationalGroup.Group) :
    classOf N (h.val*g)=classOf N g := by
  symm
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  simpa only [mul_inv_cancel_right] using h.property

/-- The fibre over a congruence class is parametrized by the projective
congruence group itself. This uses group labels, so no freeness
hypothesis on a particular point of the upper half plane is needed. -/
noncomputable def fibreEquiv (N : ℕ) (y : Classes N) :
    gamma N ≃ {g // classOf N g=y} where
  toFun h := ⟨h.val*y.out,(classOf_mul N h y.out).trans y.out_eq⟩
  invFun g := ⟨g.val*y.out⁻¹,QuotientGroup.rightRel_apply.mp
    (Quotient.exact (y.out_eq.trans g.property.symm))⟩
  left_inv h := by
    apply Subtype.ext
    simp
  right_inv g := by
    apply Subtype.ext
    simp

theorem fibre_amplitude_hasSum (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (z : ℍ) (y : Classes N) :
    HasSum (fun g : {g // classOf N g=y} => ‖amplitude N ε t (g.val • z)‖^2) 1 := by
  apply (fibreEquiv N y).hasSum_iff.mp
  simpa only [Function.comp_def,fibreEquiv,Equiv.coe_fn_mk,mul_smul] using
    amplitude_hasSum N hε ht (y.out • z)

/-- The actual quotient-to-strip isometry with the positive finite
normalizing weight proved from the integral-lattice estimate. -/
noncomputable def induction (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ) :
    ℓ²(Classes N,ℂ) →ₗᵢ[ℂ] ℓ²(AsymptoticRationalGroup.Group,ℂ) :=
  AsymptoticFiberIsometry.isometry (classOf N) (fun g => amplitude N ε t (g • z))
    (fibre_amplitude_hasSum N hε ht z)

theorem induction_apply (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (z : ℍ) (f : ℓ²(Classes N,ℂ)) (g : AsymptoticRationalGroup.Group) :
    induction N hε ht z f g=amplitude N ε t (g • z)*f (classOf N g) := rfl

theorem induction_norm (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (z : ℍ) (f : ℓ²(Classes N,ℂ)) : ‖induction N hε ht z f‖=‖f‖ :=
  (induction N hε ht z).norm_map f

#print axioms classOf_mul
#print axioms fibre_amplitude_hasSum
#print axioms induction_apply
#print axioms induction_norm

end AsymptoticCongruenceQuotient
