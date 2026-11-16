module

public import QuantitativeMaassNormalizedWeightedEmbeddingV1
public import QuantitativeMaassCompletedNewSignSpaceV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory AsymptoticClassicalPetersson

namespace QuantitativeMaass

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance

/-- The same actual completed new/sign space, viewed inside the cusp space. -/
def cuspidalNewSignSpace (N : ℕ) [NeZero N] (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN → ℂ) : Submodule ℂ (localCuspidalSpace N hN) :=
  (completedNewSignSpace N hN χ).comap (localCuspidalSpace N hN).subtype

theorem cuspidalNewSignSpace_closed (N : ℕ) [NeZero N] (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN → ℂ) :
    IsClosed (cuspidalNewSignSpace N hN χ : Set (localCuspidalSpace N hN)) :=
  (completedNewSignSpace_closed N hN χ).preimage (localCuspidalSpace N hN).subtypeL.continuous

instance cuspidalNewSignSpace_complete (N : ℕ) [NeZero N] (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN → ℂ) : CompleteSpace (cuspidalNewSignSpace N hN χ) :=
  (cuspidalNewSignSpace_closed N hN χ).completeSpace_coe

def normalizedNewSignWeightedEmbedding (N : ℕ) [NeZero N] (hN : 0<N)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (χ : admissibleGeneratorIndex N hN → ℂ) :
    cuspidalNewSignSpace N hN χ →L[ℂ] Lp ℂ 2 (quotientMeasure 0) :=
  (normalizedCuspidalWeightedEmbedding N hN hδ hν).comp (cuspidalNewSignSpace N hN χ).subtypeL

theorem normalizedCuspidalWeightedEmbedding_energy (N : ℕ) (hN : 0<N)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (x : localCuspidalSpace N hN) :
    ‖normalizedCuspidalWeightedEmbedding N hN hδ hν x‖^2=
      quotientWeightNormalization δ*‖weightedQuotientEmbedding N hδ hν x.val‖^2 := by
  rw [normalizedCuspidalWeightedEmbedding,smul_apply,norm_smul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,
    Real.sq_sqrt (quotientWeightNormalization_pos δ).le]
  rfl

theorem normalizedNewSignWeightedEmbedding_norm (N : ℕ) [NeZero N] (hN : 0<N)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (χ : admissibleGeneratorIndex N hN → ℂ) :
    ‖normalizedNewSignWeightedEmbedding N hN hδ hν χ‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  exact (normalizedCuspidalWeightedEmbedding N hN hδ hν).le_of_opNorm_le
    (normalizedCuspidalWeightedEmbedding_norm N hN hδ hν) x.val

/-- The previously proved genuine reconstruction lower bound gives one
positive normalized gap for every actual admissible new/sign sector. -/
theorem normalizedNewSignWeightedEmbedding_lower (N : ℕ) [NeZero N]
    (hN : GridAdmissibleGap.Admissible N) {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) :
    ∃ κ : ℝ,0<κ ∧ κ≤1/2 ∧ ∀ χ : admissibleGeneratorIndex N hN.1 → ℂ,(∀ i,‖χ i‖=1) →
      ∀ x : cuspidalNewSignSpace N hN.1 χ,
        κ*‖x‖^2≤‖normalizedNewSignWeightedEmbedding N hN.1 hδ hν χ x‖^2 := by
  obtain ⟨a,ha,hl⟩ := completedNewSignWeightedEmbedding_lower N hN hδ hν
  let κ := min (quotientWeightNormalization δ*a) (1/2)
  have hκ : 0<κ := lt_min (mul_pos (quotientWeightNormalization_pos δ) ha) (by norm_num)
  refine ⟨κ,hκ,min_le_right _ _,?_⟩
  intro χ hχ x
  have hh := hl χ hχ ⟨x.val.val,x.property⟩
  change a*‖x‖^2≤‖weightedQuotientEmbedding N hδ hν x.val.val‖^2 at hh
  change κ*‖x‖^2≤‖normalizedCuspidalWeightedEmbedding N hN.1 hδ hν x.val‖^2
  rw [normalizedCuspidalWeightedEmbedding_energy]
  calc
    _ ≤ (quotientWeightNormalization δ*a)*‖x‖^2 :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
    _ ≤ _ := by
      have he := mul_le_mul_of_nonneg_left hh (quotientWeightNormalization_pos δ).le
      simpa only [mul_assoc] using he

#print axioms cuspidalNewSignSpace_closed
#print axioms normalizedCuspidalWeightedEmbedding_energy
#print axioms normalizedNewSignWeightedEmbedding_norm
#print axioms normalizedNewSignWeightedEmbedding_lower

end QuantitativeMaass
