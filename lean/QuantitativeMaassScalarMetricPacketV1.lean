module

public import QuantitativeMaassAdmissibleScalarMetricV1
public import QuantitativeMaassSimilarityCountV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory AsymptoticClassicalPetersson
open scoped Topology ContDiff
namespace QuantitativeMaass

local instance (N : ℕ) [NeZero N] (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN→ℂ) : NormedAddCommGroup (completedNewSignSpace N hN χ) := inferInstance
local instance (N : ℕ) [NeZero N] (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN→ℂ) : InnerProductSpace ℂ (completedNewSignSpace N hN χ) := inferInstance

/-- The fixed explicitly constructed scalar metric. Its definition contains
no spectral parameter, source band, or target projection. -/
def admissibleScalarMetric (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) : ScalarCylinderMetric N :=
  (exists_admissible_scalar_metric N hN hδ hν).choose

theorem admissibleScalarMetric_generator_norm (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (χ : admissibleGeneratorIndex N hN.1→ℂ) (hχ : ∀ i,‖χ i‖=1)
    (x : completedGeneratorSpace N hN.1 χ) :
    ‖(admissibleScalarMetric N hN hδ hν).change (weightedQuotientEmbedding N hδ hν x.val)‖=‖x‖ :=
  (exists_admissible_scalar_metric N hN hδ hν).choose_spec χ hχ x

/-- The same scalar-metric embedding is defined on the entire quotient.
It is asserted to be isometric only on the proved generator sectors. -/
def scalarMetricQuotientEmbedding (N : ℕ) (M : ScalarCylinderMetric N)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) :
    AutomorphicSpace N→L[ℂ]Lp ℂ 2 (quotientMeasure 0) :=
  M.change.toContinuousLinearMap.comp (weightedQuotientEmbedding N hδ hν)

def scalarMetricNewSignIsometry (N : ℕ) [NeZero N] (hN : GridAdmissibleGap.Admissible N)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (χ : admissibleGeneratorIndex N hN.1→ℂ) (hχ : ∀ i,‖χ i‖=1) :
    completedNewSignSpace N hN.1 χ→ₗᵢ[ℂ]Lp ℂ 2 (quotientMeasure 0) where
  toLinearMap := ((scalarMetricQuotientEmbedding N (admissibleScalarMetric N hN hδ hν) hδ hν).comp
    (completedNewSignSpace N hN.1 χ).subtypeL).toLinearMap
  norm_map' x := admissibleScalarMetric_generator_norm N hN hδ hν χ hχ ⟨x.val,x.property.2.2⟩

/-- Canonical new/sign Gram is exactly identity after this pointwise metric
change, so no inverse Gram approximation remains in its projection. -/
theorem scalarMetricNewSignIsometry_gram (N : ℕ) [NeZero N] (hN : GridAdmissibleGap.Admissible N)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (χ : admissibleGeneratorIndex N hN.1→ℂ) (hχ : ∀ i,‖χ i‖=1) :
    (scalarMetricNewSignIsometry N hN hδ hν χ hχ).toContinuousLinearMap.adjoint.comp
      (scalarMetricNewSignIsometry N hN hδ hν χ hχ).toContinuousLinearMap=1 :=
  (scalarMetricNewSignIsometry N hN hδ hν χ hχ).adjoint_comp_self

/-- Exact intertwining on the FULL quotient, proved by similarity of the
already constructed capped cylinder packet. No weight/wave commutation is used. -/
theorem scalarMetricQuotientEmbedding_packet (N : ℕ) [NeZero N] (M : ScalarCylinderMetric N)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (f : ℝ→ℂ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f) (hc : HasCompactSupport f)
    (hr : ∀ s,star (f s)=f s) (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (x : AutomorphicSpace N) :
    similarityOperator M.change (cylinderCappedTimePacket f hf he hc hr R hR hs δ hδ ν)
      (scalarMetricQuotientEmbedding N M hδ hν x)=
      scalarMetricQuotientEmbedding N M hδ hν
        (Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f hf hc) x) := by
  change M.change (cylinderCappedTimePacket f hf he hc hr R hR hs δ hδ ν
    (M.change.symm (M.change (weightedQuotientEmbedding N hδ hν x))))=_
  rw [M.change.symm_apply_apply,weightedQuotientEmbedding_timePacket N f hf he hc hr R hR hs hδ hν]
  rfl

theorem scalarMetricNewSignIsometry_packet (N : ℕ) [NeZero N] (hN : GridAdmissibleGap.Admissible N)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (χ : admissibleGeneratorIndex N hN.1→ℂ) (hχ : ∀ i,‖χ i‖=1)
    (f : ℝ→ℂ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f) (hc : HasCompactSupport f)
    (hr : ∀ s,star (f s)=f s) (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (x : completedNewSignSpace N hN.1 χ) :
    similarityOperator (admissibleScalarMetric N hN hδ hν).change
      (cylinderCappedTimePacket f hf he hc hr R hR hs δ hδ ν)
      (scalarMetricNewSignIsometry N hN hδ hν χ hχ x)=
      scalarMetricNewSignIsometry N hN hδ hν χ hχ
        (completedNewSignTimePacket N hN.1 χ f hf he hc hr R hR hs x) :=
  scalarMetricQuotientEmbedding_packet N (admissibleScalarMetric N hN hδ hν) hδ hν
    f hf he hc hr R hR hs x.val

#print axioms admissibleScalarMetric_generator_norm
#print axioms scalarMetricNewSignIsometry_gram
#print axioms scalarMetricQuotientEmbedding_packet
#print axioms scalarMetricNewSignIsometry_packet
end QuantitativeMaass
