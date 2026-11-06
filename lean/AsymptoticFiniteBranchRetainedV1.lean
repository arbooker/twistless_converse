module

public import AsymptoticFiniteBranchCornersV1
public import AsymptoticFiniteBranchExpressionV1
public import AsymptoticBranchTraceAdditivityV1
public import AsymptoticHyperbolicAreaV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticFiniteBranch

open UpperHalfPlane MeasureTheory Filter Set ContinuousLinearMap InnerProductSpace
open AsymptoticRegularTrace AsymptoticUnweightedKernel
open scoped InnerProduct Topology

def retainedRegion (Y H : ℝ) : Set ℍ :=
  AsymptoticMassTransport.strip∩(fun z : ℍ => z.im) ⁻¹' Ico Y H

theorem retainedRegion_measurable (Y H : ℝ) : MeasurableSet (retainedRegion Y H) :=
  AsymptoticMassTransport.strip_measurable.inter (measurableSet_Ico.preimage continuous_im.measurable)

def endpointRegion (Y H : ℝ) (b : Branch) : Set ℍ :=
  retainedRegion Y H∩(fun z => b.label • z) ⁻¹' retainedRegion Y H

theorem endpointRegion_measurable (Y H : ℝ) (b : Branch) : MeasurableSet (endpointRegion Y H b) :=
  (retainedRegion_measurable Y H).inter ((retainedRegion_measurable Y H).preimage
    (AsymptoticRationalBranches.action_continuous b.label).measurable)

theorem endpointRegion_finite {Y : ℝ} (hY : 0<Y) (H : ℝ) (b : Branch) :
    IsFiniteMeasure ((volume : Measure ℍ).restrict (endpointRegion Y H b)) := by
  apply isFiniteMeasure_restrict.mpr
  apply ne_of_lt
  have hs : endpointRegion Y H b⊆AsymptoticHyperbolicArea.closedTerminal Y :=
    fun _ hz => ⟨hz.1.1,hz.1.2.1⟩
  exact (measure_mono hs).trans_lt
    ((AsymptoticHyperbolicArea.closed_terminal_area hY).trans_lt ENNReal.ofReal_lt_top)

/-- Retain both endpoints of a branch; no choice of a weight is involved. -/
noncomputable def retained (Y H : ℝ) (b : Branch) : Branch where
  label := b.label
  coefficient := (endpointRegion Y H b).indicator b.coefficient
  measurable := b.measurable.indicator (endpointRegion_measurable Y H b)
  bound := b.bound
  bound_nonneg := b.bound_nonneg
  norm_le := indicator_coefficient_bound _ _ b.bound_nonneg b.norm_le

theorem holomorphic_retained (Y H : ℝ) (b : Branch) (m : ℕ) :
    holomorphic (retained Y H b) m=
      (holomorphic (corner (retainedRegion Y H) (retainedRegion_measurable Y H)) m).comp
        ((holomorphic b m).comp
          (holomorphic (corner (retainedRegion Y H) (retainedRegion_measurable Y H)) m)) := by
  rw [← holomorphic_compose,← holomorphic_compose]
  unfold holomorphic
  simp only [compose,corner,mul_one,one_mul]
  apply AsymptoticConcreteRationalBranch.operator_congr
  intro z
  exact (corner_compose_coefficient (retainedRegion Y H) (retainedRegion Y H)
    (retainedRegion_measurable Y H) (retainedRegion_measurable Y H) b z).symm

theorem regular_retained (Y H : ℝ) (b : Branch) (z : ℍ) :
    regular (retained Y H b) z=
      (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z).comp
        ((regular b z).comp (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z)) := by
  rw [← regular_corner _ (retainedRegion_measurable Y H),← regular_compose,← regular_compose]
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext g
  simp only [regular,AsymptoticOrbitBranch.operator_apply]
  rw [corner_compose_coefficient]
  simp only [retained,compose,corner,mul_one,one_mul]
  rfl

theorem retained_diagonal_summable (h : ℕ) {ε Y : ℝ} (hε : 0<ε) (hY : 0<Y)
    (H : ℝ) (b : Branch) :
    Summable (fun n => (⟪holomorphic (retained Y H b) (h+1) (liftedMode h n hε),
      liftedMode h n hε⟫_ℂ).re) := by
  let := endpointRegion_finite hY H b
  apply branch_diagonal_summable h hε hY b.bound_nonneg _ (endpointRegion Y H b)
    (endpointRegion_measurable Y H b) (fun _ hz => hz.1.1)
    (fun z => b.label • z) (AsymptoticRationalBranches.action_continuous b.label).measurable
    (fun z => b.coefficient z*AsymptoticSlashGauge.phase b.label (h+1) z)
  · exact (b.measurable.mul (AsymptoticSlashGauge.phase_continuous b.label (h+1)).measurable).aestronglyMeasurable
  · apply Eventually.of_forall
    intro z
    simpa only [norm_mul,AsymptoticSlashGauge.phase_norm,mul_one] using b.norm_le z
  · exact (ae_restrict_mem (endpointRegion_measurable Y H b)).mono
      (fun _ hz => ⟨hz.2.2.1,hz.1.2.1,hz.2.2.2.le,hz.1.2.2.le⟩)
  · intro n
    exact AsymptoticConcreteRationalBranch.retained_operator_mode b.label (endpointRegion Y H b)
      (endpointRegion_measurable Y H b) (fun _ hz => hz.2.1)
      b.coefficient b.measurable b.bound_nonneg b.norm_le h n hε

theorem retained_root_integrable {Y : ℝ} (hY : 0<Y) (H : ℝ) (b : Branch) :
    Integrable (fun z => (matrix (regular (retained Y H b) z) 1 1).re) volume := by
  classical
  let := endpointRegion_finite hY H b
  simp only [regular,AsymptoticOrbitBranch.operator_root,retained]
  by_cases hb : b.label=1
  · simp only [hb,ite_true]
    have hi : Integrable b.coefficient ((volume : Measure ℍ).restrict (endpointRegion Y H b)) :=
      (integrable_const b.bound).mono' b.measurable.aestronglyMeasurable (Eventually.of_forall b.norm_le)
    change IntegrableOn b.coefficient (endpointRegion Y H b) volume at hi
    have hh := hi.integrable_indicator (endpointRegion_measurable Y H b)
    exact hh.re
  · simp only [hb,ite_false,Complex.zero_re]
    exact integrable_zero _ _ _

/-- Every retained concrete branch has the regular rooted coefficient
as its normalized large-weight trace. -/
theorem retained_trace_tendsto {ε Y : ℝ} (hε : 0<ε) (hY : 0<Y) (H : ℝ) (b : Branch) :
    Tendsto (fun h => liftedTrace h hε (holomorphic (retained Y H b) (h+1))/(2*h+2:ℕ))
      atTop (𝓝 (signedTrace volume (regular (retained Y H b))/(4*Real.pi))) := by
  let := endpointRegion_finite hY H b
  exact AsymptoticConcreteRationalBranch.retained_operator_trace_tendsto hε hY b.bound_nonneg
    b.label (endpointRegion Y H b) (endpointRegion_measurable Y H b) (fun _ hz => hz.1.1)
    b.coefficient b.measurable b.norm_le (fun _ hz => hz.2.1)
    ((ae_restrict_mem (endpointRegion_measurable Y H b)).mono
      (fun _ hz => ⟨hz.2.2.1,hz.1.2.1,hz.2.2.2.le,hz.1.2.2.le⟩))

#print axioms endpointRegion_finite
#print axioms holomorphic_retained
#print axioms regular_retained
#print axioms retained_diagonal_summable
#print axioms retained_root_integrable
#print axioms retained_trace_tendsto

end AsymptoticFiniteBranch
