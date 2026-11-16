module

public import QuantitativeMaassCoverMetricCompletionV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology MatrixGroups
namespace QuantitativeMaass

/-- A bounded positive pointwise change of the cylinder metric, with its
actual inverse and the invariant coefficient recorded explicitly. -/
structure ScalarCylinderMetric (N : ℕ) where
  weight : ℍ→ℝ
  measurable : Measurable weight
  invariant : ∀ a : gamma N,∀ z,weight (a.val • z)=weight z
  lower : ℝ
  upper : ℝ
  lower_pos : 0<lower
  bounds : ∀ z,lower≤weight z ∧ weight z≤upper
  change : Lp ℂ 2 (quotientMeasure 0) ≃L[ℂ] Lp ℂ 2 (quotientMeasure 0)
  coeFn : ∀ f : Lp ℂ 2 (quotientMeasure 0),
    (change f : ℍ→ℂ)=ᵐ[quotientMeasure 0]fun z => (weight z:ℂ)*f z
  norm_le : ‖change.toContinuousLinearMap‖≤upper
  inv_norm_le : ‖change.symm.toContinuousLinearMap‖≤lower⁻¹

def normalizerCoverScalarMetric {ι : Type*} [Fintype ι] [Nonempty ι]
    (N : ℕ) (g : ι→quotientNormalizerGroup N)
    {δ Y : ℝ} (hδ : 0<δ) (hY : 0<Y) {ν : ℕ} (hν : 1≤ν)
    (hcover : ∀ z : ℍ,∃ i,∃ a : gamma N,Y≤(a.val • ((g i).val • z)).im) :
    ScalarCylinderMetric N where
  weight := normalizerCoverMetric N g δ ν
  measurable := normalizerCoverMetric_measurable N g δ ν
  invariant := normalizerCoverMetric_invariant N g δ ν
  lower := Real.sqrt (((Fintype.card ι:ℝ)*quotientWeightBound δ+1)⁻¹)
  upper := Real.sqrt ((Fintype.card ι:ℝ)/heightWeightFloor δ ν Y)
  lower_pos := Real.sqrt_pos.mpr (inv_pos.mpr (by
    have hh := quotientWeightBound_nonneg δ
    have hm : (0:ℝ)≤Fintype.card ι := Nat.cast_nonneg _
    positivity))
  bounds := normalizerCoverMetric_bounds N g hδ hY hν hcover
  change := normalizerCoverMetricEquiv N g hδ hY hν hcover
  coeFn := normalizerCoverMetricEquiv_coeFn N g hδ hY hν hcover
  norm_le := positiveL2MultiplierEquiv_norm _ _ _ _ _ (Real.sqrt_nonneg _)
  inv_norm_le := positiveL2MultiplierEquiv_symm_norm _ _ _ _ _

/-- An actual scalar metric, common to all sign sectors, makes their
weighted quotient embeddings exactly isometric. This uses the constructed
finite cusp cover and no spectral projection or inverse Gram polynomial. -/
theorem exists_admissible_scalar_metric (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) :
    ∃ M : ScalarCylinderMetric N,
      ∀ χ : admissibleGeneratorIndex N hN.1→ℂ,(∀ i,‖χ i‖=1) →
      ∀ x : completedGeneratorSpace N hN.1 χ,
        ‖M.change (weightedQuotientEmbedding N hδ hν x.val)‖=‖x‖ := by
  classical
  let : NeZero N := ⟨hN.1.ne'⟩
  let := Fintype.ofFinite (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  obtain ⟨g,hg,hc,hci,Y,hY,hcover⟩ := admissible_generator_height_cover N hN
  let g' (q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) : quotientNormalizerGroup N :=
    ⟨g q,normalizer_mem_of_conjugations N (g q) (hc q) (hci q)⟩
  refine ⟨normalizerCoverScalarMetric N g' hδ hY hν hcover,?_⟩
  intro χ hχ x
  apply normalizerCoverMetric_completed_norm N g' hδ hY hν hcover x.val
  intro q
  have hsub : admissibleNormalizerGroup N hN.1≤
      (normalizerEigenStabilizer N x.val).map (quotientNormalizerGroup N).subtype := by
    rw [admissibleNormalizerGroup,Subgroup.closure_le]
    intro a ha
    refine ⟨admissibleGeneratorLift N hN.1 ⟨a,ha⟩,?_,rfl⟩
    exact ⟨χ ⟨a,ha⟩,hχ ⟨a,ha⟩,x.property ⟨a,ha⟩⟩
  obtain ⟨a,ha,he⟩ := hsub (hg q)
  have heq : a=g' q := Subtype.ext he
  exact heq ▸ ha

#print axioms normalizerCoverScalarMetric
#print axioms exists_admissible_scalar_metric
end QuantitativeMaass
