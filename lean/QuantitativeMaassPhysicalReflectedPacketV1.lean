module

public import QuantitativeMaassConcreteBranchPacketV1
public import QuantitativeMaassPhysicalReflectionV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticClassicalPetersson AsymptoticFiniteBranch AsymptoticMassTransport
open scoped SchwartzMap ContDiff
namespace QuantitativeMaass

variable (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
  (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
  (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)

include hr in
/-- The compact physical reflected branch is its actual cylinder column
operator, including the input-strip indicator at the reflected image. -/
theorem physical_reflected_branch_packet_eq_column (b : Branch) (S : Set ℍ) (hS : IsCompact S)
    (v : Lp ℂ 2 (quotientMeasure 0)) :
    AsymptoticZeroExtension.isometry volume S hS.measurableSet
      (cylinderBranchColumnPacket f hc he R hR hs S hS
        (fun z => b.label • (J•z))
        ((AsymptoticRationalBranches.action_continuous b.label).comp (continuous_const_smul J))
        (fun z => cylinderInputBranchCoefficient b (J•z))
        ((cylinderInputBranchCoefficient_measurable b).comp (continuous_const_smul J).measurable).aestronglyMeasurable
        b.bound (Eventually.of_forall (fun z => cylinderInputBranchCoefficient_bound b (J•z))) v) =
      AsymptoticRegionL2.projection volume S hS.measurableSet
        (physicalReflection (holomorphic b 0 (cylinderZeroExtension (cylinderTimePacket f (f.smooth ⊤) hc v)))) := by
  let a := fun z => cylinderInputBranchCoefficient b (J•z)
  let u := fun z : ℍ => b.label • (J•z)
  have hu : Continuous u :=
    (AsymptoticRationalBranches.action_continuous b.label).comp (continuous_const_smul J)
  have ha : Measurable a :=
    (cylinderInputBranchCoefficient_measurable b).comp (continuous_const_smul J).measurable
  have hb : ∀ᵐ z ∂volume.restrict S,‖a z‖≤b.bound :=
    Eventually.of_forall (fun z => cylinderInputBranchCoefficient_bound b (J•z))
  let C := cylinderBranchColumnPacket f hc he R hR hs S hS u hu a ha.aestronglyMeasurable b.bound hb
  have hcol := finiteEnergyColumnOperator_coeFn (volume.restrict S)
    (fun x => star (a x) • cylinderTimeColumn f hc he R hR hs (u x))
    (compact_branch_column_memLp _ (cylinderAbelColumn_continuous _ _ R hR _)
      S hS u hu a ha.aestronglyMeasurable b.bound hb) v
  have hz := AsymptoticZeroExtension.isometry_coeFn volume S hS.measurableSet (C v)
  have hz' := hz.trans ((ae_eq_restrict_iff_indicator_ae_eq hS.measurableSet).mp hcol)
  let ψ := fun z => inner ℂ (cylinderTimeColumn f hc he R hR hs z) v
  have hw := cylinderZeroExtension_coeFn_of_ae (cylinderTimePacket f (f.smooth ⊤) hc v) ψ
    (cylinderTimePacket_column_coeFn f (f.smooth ⊤) he hc hr R hR hs
      (evenCoshLift_support_of_time_support f R hR hs) v)
  have hp := physicalReflection_representative
    (holomorphic b 0 (cylinderZeroExtension (cylinderTimePacket f (f.smooth ⊤) hc v)))
    (branchFunction b (strip.indicator ψ)) (physical_branch_representative b _ _ hw)
  apply Lp.ext
  filter_upwards [hz',hp,AsymptoticRegionL2.projection_coeFn volume S hS.measurableSet
    (physicalReflection (holomorphic b 0 (cylinderZeroExtension (cylinderTimePacket f (f.smooth ⊤) hc v))))]
    with z h1 h2 h3
  rw [h1,h3]
  classical
  by_cases hzS : z∈S
  · rw [indicator_of_mem hzS,indicator_of_mem hzS,h2]
    change inner ℂ (star (a z) • cylinderTimeColumn f hc he R hR hs (u z)) v =
      b.coefficient (J•z)*strip.indicator ψ (u z)
    simp only [inner_smul_left,starRingEnd_apply,star_star]
    by_cases hzB : u z∈strip
    · have ha' : a z=b.coefficient (J•z) :=
        indicator_of_mem (show J•z ∈ (fun w : ℍ => b.label • w) ⁻¹' strip from hzB) _
      rw [ha',indicator_of_mem hzB]
    · have ha' : a z=0 :=
        indicator_of_notMem (show J•z ∉ (fun w : ℍ => b.label • w) ⁻¹' strip from hzB) _
      rw [ha',indicator_of_notMem hzB,zero_mul,mul_zero]
  · rw [indicator_of_notMem hzS,indicator_of_notMem hzS]

include hr in
theorem physical_reflected_branch_packet_trace {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0)))
    (b : Branch) (S : Set ℍ) (hS : IsCompact S) :
    (∑' i,(inner ℂ
      (AsymptoticZeroExtension.isometry volume S hS.measurableSet
        (cylinderCompactColumnPacket f hc he R hR hs S hS (basis i)))
      (AsymptoticRegionL2.projection volume S hS.measurableSet
        (physicalReflection (holomorphic b 0
          (cylinderZeroExtension (cylinderTimePacket f (f.smooth ⊤) hc (basis i))))))).re) =
      ∫ x in S,(cylinderInputBranchCoefficient b (J•x)*radialPoincareKernel 0
        (abelProfile (evenCoshLift (timeConvolution f f))) x (b.label • (J•x))).re := by
  simp_rw [←physical_reflected_branch_packet_eq_column f hc he hr R hR hs b S hS]
  simp only [(AsymptoticZeroExtension.isometry volume S hS.measurableSet).inner_map_map]
  exact cylinder_compact_branch_trace f hc he hr R hR hs basis S hS
    (fun x => b.label • (J•x))
    ((AsymptoticRationalBranches.action_continuous b.label).comp (continuous_const_smul J))
    (fun x => cylinderInputBranchCoefficient b (J•x))
    ((cylinderInputBranchCoefficient_measurable b).comp (continuous_const_smul J).measurable).aestronglyMeasurable
    b.bound (Eventually.of_forall (fun x => cylinderInputBranchCoefficient_bound b (J•x)))

#print axioms physical_reflected_branch_packet_eq_column
#print axioms physical_reflected_branch_packet_trace

end QuantitativeMaass
