module

public import QuantitativeMaassCylinderColumnApproxV1
public import QuantitativeMaassCylinderTimePacketV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- The original even smooth time packet on the infinite-volume translation
cylinder has the literal Abel kernel on every L2 input. -/
theorem cylinderTimePacket_kernel_coeFn (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (hc : HasCompactSupport f) (hr : ∀ s,star (f s)=f s)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (v : Lp ℂ 2 (quotientMeasure 0)) :
    cylinderTimePacket f hf hc v=ᵐ[quotientMeasure 0]
      (fun x => ∫ y,radialPoincareKernel 0 (abelProfile (evenCoshLift f)) x y*v y ∂quotientMeasure 0) := by
  let a : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have ha (n : ℕ) : 0<a n := by dsimp [a]; positivity
  have ha0 : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let F := evenCoshLift f
  have hF : ContDiffOn ℝ ∞ F (Ici 1) := evenCoshLift_smoothOn f hf he hc
  have hz : ∀ q,Real.cosh R<q → F q=0 := evenCoshLift_zero_above f R hR hs
  have hsF : Function.support F⊆Iic (Real.cosh R) := by
    intro q hq
    by_contra hn
    exact hq (hz q (lt_of_not_ge hn))
  let T (n : ℕ) := cylinderTimePacket (radialShiftTime f (a n))
    (radialShiftTime_smooth f hf he hc (a n) (ha n))
    (radialShiftTime_compact f R hR hs (a n) (ha n))
  let C (n : ℕ) (x : ℍ) := cylinderAbelColumn (radialShiftApprox F (a n))
    (radialShiftApprox_smooth F hF _ (ha n)).contDiffOn R hR
    (radialShiftApprox_upper_support F _ hz _ (ha n)) x
  have hT : Tendsto (fun n => T n v) atTop (𝓝 (cylinderTimePacket f hf hc v)) :=
    ((ContinuousLinearMap.apply ℂ (Lp ℂ 2 (quotientMeasure 0)) v).continuous.tendsto _).comp
      (cylinderTimePacket_shift_tendsto atTop f hf he hc R hR hs a ha ha0)
  apply L2_limit_eq_pointwise_representatives (quotientMeasure 0) _ _ hT
    (fun n x => inner ℂ (C n x) v)
  · intro n
    have hFn := radialShiftApprox_smooth F hF _ (ha n)
    have hFnc := radialShiftApprox_compact F _ hz _ (ha n)
    have hFnr := radialShiftApprox_real F (evenCoshLift_real f hr) (a n)
    have hFns := radialShiftApprox_upper_support F _ hz _ (ha n)
    have heq : T n=(radialKernelData 0 (abelProfile (radialShiftApprox F (a n)))
      (abelProfile_smooth _ hFn hFnc) R hR (abelProfile_support _ _ hFns)).operator :=
      cylinderTimePacket_cosh _ hFn hFnc hFnr R hR hFns
    rw [heq]
    have hh := (radialKernelData 0 (abelProfile (radialShiftApprox F (a n)))
      (abelProfile_smooth _ hFn hFnc) R hR (abelProfile_support _ _ hFns)).operator_coeFn v
    apply hh.trans
    filter_upwards with x
    exact (cylinderAbelColumn_inner _ hFn.contDiffOn hFnr R hR hFns x v).symm
  · intro x
    have hC : Tendsto (fun n => C n x) atTop (𝓝 (cylinderAbelColumn F hF R hR hsF x)) :=
      cylinderAbelColumn_shift_tendsto atTop F hF R hR hsF a ha ha0 x
    have hh := hC.inner (𝕜:=ℂ) (tendsto_const_nhds (x:=v))
    rwa [cylinderAbelColumn_inner F hF (evenCoshLift_real f hr) R hR hsF] at hh

/-- The actual wave output is represented by pairing against its continuous
literal cylinder column. -/
theorem cylinderTimePacket_column_coeFn (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (hc : HasCompactSupport f) (hr : ∀ s,star (f s)=f s)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (hsF : Function.support (evenCoshLift f)⊆Iic (Real.cosh R))
    (v : Lp ℂ 2 (quotientMeasure 0)) :
    cylinderTimePacket f hf hc v=ᵐ[quotientMeasure 0]
      (fun x => inner ℂ (cylinderAbelColumn (evenCoshLift f) (evenCoshLift_smoothOn f hf he hc)
        R hR hsF x) v) := by
  apply (cylinderTimePacket_kernel_coeFn f hf he hc hr R hR hs v).trans
  filter_upwards with x
  exact (cylinderAbelColumn_inner _ _ (evenCoshLift_real f hr) R hR hsF x v).symm

#print axioms cylinderTimePacket_kernel_coeFn
#print axioms cylinderTimePacket_column_coeFn

end QuantitativeMaass
