module

public import QuantitativeMaassCylinderBranchTraceV1
public import QuantitativeMaassColumnFiniteTraceV1
public import QuantitativeMaassCylinderPhysicalV1
public import AsymptoticFiniteBranchDataV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticClassicalPetersson AsymptoticFiniteBranch
open scoped SchwartzMap ContDiff
namespace QuantitativeMaass

/-- The branch input is the actual zero-extended cylinder, so its input-strip
indicator is retained in the coefficient. -/
def cylinderInputBranchCoefficient (b : Branch) : ℍ→ℂ :=
  ((fun z : ℍ => b.label • z) ⁻¹' AsymptoticMassTransport.strip).indicator b.coefficient

theorem cylinderInputBranchCoefficient_measurable (b : Branch) :
    Measurable (cylinderInputBranchCoefficient b) :=
  b.measurable.indicator (AsymptoticMassTransport.strip_measurable.preimage
    (AsymptoticRationalBranches.action_continuous b.label).measurable)

theorem cylinderInputBranchCoefficient_bound (b : Branch) (z : ℍ) :
    ‖cylinderInputBranchCoefficient b z‖≤b.bound := by
  exact (norm_indicator_le_norm_self b.coefficient z).trans (b.norm_le z)

variable (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
  (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
  (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)

include hr in
/-- A finite rational branch acting on the genuine cylinder wave packet,
with compact output restriction, is exactly the constructed branch-column
operator. This identifies the operator before estimating its trace. -/
theorem concrete_branch_packet_eq_column (b : Branch) (S : Set ℍ) (hS : IsCompact S)
    (v : Lp ℂ 2 (quotientMeasure 0)) :
    AsymptoticZeroExtension.isometry volume S hS.measurableSet
      (cylinderBranchColumnPacket f hc he R hR hs S hS
        (fun z => b.label • z) (AsymptoticRationalBranches.action_continuous b.label)
        (cylinderInputBranchCoefficient b) (cylinderInputBranchCoefficient_measurable b).aestronglyMeasurable
        b.bound (Eventually.of_forall (cylinderInputBranchCoefficient_bound b)) v)=
      AsymptoticRegionL2.projection volume S hS.measurableSet
        (holomorphic b 0 (cylinderZeroExtension (cylinderTimePacket f (f.smooth ⊤) hc v))) := by
  let a := cylinderInputBranchCoefficient b
  let C := cylinderBranchColumnPacket f hc he R hR hs S hS
    (fun z => b.label • z) (AsymptoticRationalBranches.action_continuous b.label)
    a (cylinderInputBranchCoefficient_measurable b).aestronglyMeasurable
    b.bound (Eventually.of_forall (cylinderInputBranchCoefficient_bound b))
  have hcol := finiteEnergyColumnOperator_coeFn (volume.restrict S)
    (fun x => star (a x) • cylinderTimeColumn f hc he R hR hs (b.label • x))
    (compact_branch_column_memLp _ (cylinderAbelColumn_continuous _ _ R hR _) S hS
      (fun z => b.label • z) (AsymptoticRationalBranches.action_continuous b.label)
      a (cylinderInputBranchCoefficient_measurable b).aestronglyMeasurable
      b.bound (Eventually.of_forall (cylinderInputBranchCoefficient_bound b))) v
  have hz := AsymptoticZeroExtension.isometry_coeFn volume S hS.measurableSet (C v)
  have hz' := hz.trans ((ae_eq_restrict_iff_indicator_ae_eq hS.measurableSet).mp hcol)
  have hw := cylinderZeroExtension_coeFn_of_ae (cylinderTimePacket f (f.smooth ⊤) hc v) _
    (cylinderTimePacket_column_coeFn f (f.smooth ⊤) he hc hr R hR hs
      (evenCoshLift_support_of_time_support f R hR hs) v)
  have hmove := (AsymptoticRationalGroup.measurePreserving b.label).quasiMeasurePreserving.ae hw
  apply Lp.ext
  filter_upwards [hz',AsymptoticRegionL2.projection_coeFn volume S hS.measurableSet
      (holomorphic b 0 (cylinderZeroExtension (cylinderTimePacket f (f.smooth ⊤) hc v))),
    AsymptoticConcreteRationalBranch.operator_coeFn b.label b.coefficient b.measurable b.norm_le 0
      (cylinderZeroExtension (cylinderTimePacket f (f.smooth ⊤) hc v)),hmove] with z h1 h2 h3 h4
  rw [h1,h2]
  classical
  by_cases hzS : z∈S
  · rw [indicator_of_mem hzS,indicator_of_mem hzS]
    change _=holomorphic b 0 (cylinderZeroExtension (cylinderTimePacket f (f.smooth ⊤) hc v)) z
    change holomorphic b 0 (cylinderZeroExtension (cylinderTimePacket f (f.smooth ⊤) hc v)) z=_ at h3
    rw [h3,h4]
    simp only [inner_smul_left,starRingEnd_apply,star_star]
    have hphase : AsymptoticSlashGauge.phase b.label 0 z=1 := by
      simp only [AsymptoticSlashGauge.phase,AsymptoticHyperbolicSlash.phase,mul_zero,pow_zero]
    rw [hphase,mul_one]
    by_cases hzB : b.label • z∈AsymptoticMassTransport.strip
    · have ha : a z=b.coefficient z :=
        indicator_of_mem (show z∈(fun z : ℍ => b.label • z) ⁻¹' AsymptoticMassTransport.strip from hzB) _
      rw [ha,indicator_of_mem hzB]
      rfl
    · have ha : a z=0 :=
        indicator_of_notMem (show z∉(fun z : ℍ => b.label • z) ⁻¹' AsymptoticMassTransport.strip from hzB) _
      rw [ha,indicator_of_notMem hzB,zero_mul,mul_zero]

  · rw [indicator_of_notMem hzS,indicator_of_notMem hzS]

include hr in
/-- Exact mixed trace of a literal rational pullback on the physical
cylinder packet, with both compact and input-strip restrictions retained. -/
theorem concrete_branch_packet_trace {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0)))
    (b : Branch) (S : Set ℍ) (hS : IsCompact S) :
    (∑' i,(inner ℂ
      (AsymptoticZeroExtension.isometry volume S hS.measurableSet
        (cylinderCompactColumnPacket f hc he R hR hs S hS (basis i)))
      (AsymptoticRegionL2.projection volume S hS.measurableSet
        (holomorphic b 0 (cylinderZeroExtension (cylinderTimePacket f (f.smooth ⊤) hc (basis i)))))).re)=
      ∫ x in S,(cylinderInputBranchCoefficient b x*radialPoincareKernel 0
        (abelProfile (evenCoshLift (timeConvolution f f))) x (b.label • x)).re := by
  simp_rw [←concrete_branch_packet_eq_column f hc he hr R hR hs b S hS]
  simp only [(AsymptoticZeroExtension.isometry volume S hS.measurableSet).inner_map_map]
  exact cylinder_compact_branch_trace f hc he hr R hR hs basis S hS
    (fun x => b.label • x) (AsymptoticRationalBranches.action_continuous b.label)
    (cylinderInputBranchCoefficient b) (cylinderInputBranchCoefficient_measurable b).aestronglyMeasurable
    b.bound (Eventually.of_forall (cylinderInputBranchCoefficient_bound b))

#print axioms cylinderInputBranchCoefficient_measurable
#print axioms cylinderInputBranchCoefficient_bound
#print axioms concrete_branch_packet_eq_column
#print axioms concrete_branch_packet_trace
end QuantitativeMaass
