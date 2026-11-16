module

public import QuantitativeMaassCylinderCorrespondenceBoundV1
public import QuantitativeMaassCorrespondenceIdentityV1
public import QuantitativeMaassCylinderBranchTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff FourierTransform SchwartzMap ENNReal

namespace QuantitativeMaass

attribute [local instance] Classical.propDecidable

/-- The actual positive integral cylinder branch differs from its literal
identity-coset term by the explicit nonscalar geometric error. Bounded
measurable coefficients are permitted. -/
theorem cylinder_weighted_correspondence_error
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
    (B : ℝ) (hB : 0<B) (hentry : ∀ i j,|(M i j:ℝ)|≤B)
    (o : ℍ) (L R : ℝ) (hR : 0≤R) (g : ℝ→ℂ) (hg : ContinuousOn g (Ici 1))
    (hs : Function.support g⊆Iic (Real.cosh R)) (C : ℝ) (hC : 0≤C)
    (hb : ∀ d : ℝ,0<d → ‖g (Real.cosh d)‖≤C/Real.sqrt (Real.sinh d))
    (a : ℍ→ℂ) (ha : AEStronglyMeasurable a (volume.restrict (Metric.closedBall o L)))
    (A : ℝ) (hA : 0≤A) (haB : ∀ᵐ x ∂volume.restrict (Metric.closedBall o L),‖a x‖≤A) :
    |(∫ x in Metric.closedBall o L,(a x*radialPoincareKernel 0 g x (positiveIntegralGL M hM • x)).re)-
      (∫ x in Metric.closedBall o L,(a x*(if integralIdentityCoset 0 M then g 1 else 0)).re)|≤
      A*((QuantitativeArithmeticMaassOverlap.energyMultiplicity o 0
        (R+2*L+dist (positiveIntegralGL M hM • o) o):ℝ)*C*
        (Real.pi*(volume.real (Metric.closedBall o L)+
          hyperbolicSublevelConstant o L (R+2*L+dist (positiveIntegralGL M hM • o) o+2*Real.log (2*B))))) := by
  classical
  let S := Metric.closedBall o L
  let E := radialIntegralRemainder 0 M hM g
  let I : ℂ := if integralIdentityCoset 0 M then g 1 else 0
  obtain ⟨hi,hbound⟩ := radialIntegralRemainder_all_integral_bound 0 M hM B hB hentry o L R hR g hg hs C hC hb
  have hiE : IntegrableOn (fun x => a x*E x) S := by
    apply (hi.norm.const_mul A).mono' (ha.mul hi.aestronglyMeasurable)
    filter_upwards [haB] with x hx
    change ‖a x*E x‖≤A*‖E x‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  have hiI : IntegrableOn (fun x => a x*I) S := by
    have hconst : IntegrableOn (fun _x : ℍ => A*‖I‖) S :=
      continuous_const.continuousOn.integrableOn_compact (isCompact_closedBall o L)
    apply hconst.mono' (ha.mul aestronglyMeasurable_const)
    filter_upwards [haB] with x hx
    change ‖a x*I‖≤A*‖I‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  have hsplit (x : ℍ) : radialPoincareKernel 0 g x (positiveIntegralGL M hM • x)=I+E x :=
    radialIntegralKernel_identity_split 0 M hM g R hR hs x
  conv =>
    lhs
    simp only [hsplit,mul_add,Complex.add_re]
  change |(∫ x in S,(a x*I).re+(a x*E x).re)-(∫ x in S,(a x*I).re)|≤_
  have hiIr : IntegrableOn (fun x => (a x*I).re) S := hiI.re
  have hiEr : IntegrableOn (fun x => (a x*E x).re) S := hiE.re
  rw [integral_add hiIr hiEr,add_sub_cancel_left,←Real.norm_eq_abs]
  calc
    _≤∫ x in S,A*‖E x‖ := by
      apply norm_integral_le_of_norm_le (hi.norm.const_mul A)
      filter_upwards [haB] with x hx
      calc
        _≤‖a x*E x‖ := by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (a x*E x)
        _=‖a x‖*‖E x‖ := norm_mul _ _
        _≤_ := mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    _=A*(∫ x in S,‖E x‖) := integral_const_mul _ _
    _≤_ := mul_le_mul_of_nonneg_left hbound hA

#print axioms cylinder_weighted_correspondence_error

end QuantitativeMaass
