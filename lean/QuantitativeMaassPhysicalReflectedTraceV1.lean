module

public import QuantitativeMaassPhysicalReflectedPacketV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticClassicalPetersson AsymptoticFiniteBranch
open scoped SchwartzMap ContDiff
namespace QuantitativeMaass

variable (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
  (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
  (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
  {ι : Type*} [Countable ι] (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0)))
  (S : Set ℍ) (hS : IsCompact S)

include hr in
theorem physical_reflected_branch_packet_summable (b : Branch) :
    Summable (fun i => (inner ℂ
      (AsymptoticZeroExtension.isometry volume S hS.measurableSet
        (cylinderCompactColumnPacket f hc he R hR hs S hS (basis i)))
      (AsymptoticRegionL2.projection volume S hS.measurableSet
        (physicalReflection (holomorphic b 0
          (cylinderZeroExtension (cylinderTimePacket f (f.smooth ⊤) hc (basis i))))))).re) := by
  simp_rw [←physical_reflected_branch_packet_eq_column f hc he hr R hR hs b S hS]
  simp only [(AsymptoticZeroExtension.isometry volume S hS.measurableSet).inner_map_map]
  exact finiteEnergyColumn_pair_summable _ _ _ _ _ basis

include hr in
theorem physical_reflected_expression_packet_summable (E : Expression) :
    Summable (fun i => (inner ℂ
      (AsymptoticZeroExtension.isometry volume S hS.measurableSet
        (cylinderCompactColumnPacket f hc he R hR hs S hS (basis i)))
      (AsymptoticRegionL2.projection volume S hS.measurableSet
        (physicalReflection (holomorphicSum E 0
          (cylinderZeroExtension (cylinderTimePacket f (f.smooth ⊤) hc (basis i))))))).re) := by
  induction E with
  | nil =>
    simpa only [holomorphicSum,List.map_nil,List.sum_nil,zero_apply,map_zero,inner_zero_right,Complex.zero_re]
      using summable_zero
  | cons b E ih =>
    simpa only [holomorphicSum,List.map_cons,List.sum_cons,add_apply,map_add,inner_add_right,Complex.add_re]
      using (physical_reflected_branch_packet_summable f hc he hr R hR hs basis S hS b).add ih

include hr in
/-- Absolutely convergent kernel trace of the actual reflected finite
expression. Each input-strip indicator remains in its coefficient. -/
theorem physical_reflected_expression_packet_trace (E : Expression) :
    (∑' i,(inner ℂ
      (AsymptoticZeroExtension.isometry volume S hS.measurableSet
        (cylinderCompactColumnPacket f hc he R hR hs S hS (basis i)))
      (AsymptoticRegionL2.projection volume S hS.measurableSet
        (physicalReflection (holomorphicSum E 0
          (cylinderZeroExtension (cylinderTimePacket f (f.smooth ⊤) hc (basis i))))))).re) =
      (E.map (fun b => ∫ x in S,(cylinderInputBranchCoefficient b (J•x)*radialPoincareKernel 0
        (abelProfile (evenCoshLift (timeConvolution f f))) x (b.label • (J•x))).re)).sum := by
  induction E with
  | nil =>
    simp only [holomorphicSum,List.map_nil,List.sum_nil,zero_apply,map_zero,inner_zero_right,Complex.zero_re,tsum_zero]
  | cons b E ih =>
    change (∑' i,(inner ℂ _ (AsymptoticRegionL2.projection volume S hS.measurableSet
      (physicalReflection ((holomorphic b 0+holomorphicSum E 0)
        (cylinderZeroExtension (cylinderTimePacket f (f.smooth ⊤) hc (basis i))))))).re)=_
    simp only [add_apply,map_add,inner_add_right,Complex.add_re,List.map_cons,List.sum_cons]
    rw [Summable.tsum_add (physical_reflected_branch_packet_summable f hc he hr R hR hs basis S hS b)
      (physical_reflected_expression_packet_summable f hc he hr R hR hs basis S hS E),
      physical_reflected_branch_packet_trace f hc he hr R hR hs basis b S hS,ih]

#print axioms physical_reflected_branch_packet_summable
#print axioms physical_reflected_expression_packet_summable
#print axioms physical_reflected_expression_packet_trace

end QuantitativeMaass
