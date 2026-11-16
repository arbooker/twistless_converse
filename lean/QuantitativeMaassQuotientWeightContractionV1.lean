module

public import QuantitativeMaassCuspidalQuotientWeightGramV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeMaass

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) :=
  inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) :=
  inferInstance

theorem cuspidalQuotientWeight_norm (N : ℕ) (hN : 0<N) {δ : ℝ} (hδ : 0<δ)
    {ν : ℕ} (hν : 1≤ν) : ‖cuspidalQuotientWeight N hN hδ hν‖≤quotientWeightBound δ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (quotientWeightBound_nonneg δ)
  intro x
  apply ((localCuspidalSpace N hN).norm_orthogonalProjectionOnto_apply_le _).trans
  exact (quotientWeightAutomorphicMultiplier N hδ hν).le_of_opNorm_le
    (quotientWeightAutomorphicMultiplier_norm N hδ hν) x

def cuspidalQuotientWeightEndomorphism (N : ℕ) (hN : 0<N) {δ : ℝ} (hδ : 0<δ)
    {ν : ℕ} (hν : 1≤ν) : localCuspidalSpace N hN →L[ℂ] localCuspidalSpace N hN :=
  (cuspidalQuotientWeight N hN hδ hν).comp (localCuspidalSpace N hN).subtypeL

theorem cuspidalQuotientWeightEndomorphism_norm (N : ℕ) (hN : 0<N)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) :
    ‖cuspidalQuotientWeightEndomorphism N hN hδ hν‖≤quotientWeightBound δ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (quotientWeightBound_nonneg δ)
  intro x
  exact (cuspidalQuotientWeight N hN hδ hν).le_of_opNorm_le
    (cuspidalQuotientWeight_norm N hN hδ hν) x.val

def quotientWeightNormalization (δ : ℝ) : ℝ := (quotientWeightBound δ+1)⁻¹

theorem quotientWeightNormalization_pos (δ : ℝ) : 0<quotientWeightNormalization δ := by
  unfold quotientWeightNormalization
  exact inv_pos.mpr (by linarith [quotientWeightBound_nonneg δ])

theorem quotientWeightNormalization_le_one (δ : ℝ) : quotientWeightNormalization δ≤1 := by
  apply (inv_le_one₀ (by linarith [quotientWeightBound_nonneg δ] : 0<quotientWeightBound δ+1)).mpr
  linarith [quotientWeightBound_nonneg δ]

theorem quotientWeightNormalization_complex_norm (δ : ℝ) :
    ‖(quotientWeightNormalization δ:ℂ)‖=quotientWeightNormalization δ := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (quotientWeightNormalization_pos δ)]

/-- A fixed explicit scalar normalizes the actual cuspidal Gram to a contraction.
The original operator is recovered by multiplication by B+1. -/
def normalizedCuspidalQuotientWeight (N : ℕ) (hN : 0<N) {δ : ℝ} (hδ : 0<δ)
    {ν : ℕ} (hν : 1≤ν) : localCuspidalSpace N hN →L[ℂ] localCuspidalSpace N hN :=
  (quotientWeightNormalization δ:ℂ) • cuspidalQuotientWeightEndomorphism N hN hδ hν

theorem normalizedCuspidalQuotientWeight_norm (N : ℕ) (hN : 0<N)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) :
    ‖normalizedCuspidalQuotientWeight N hN hδ hν‖≤1 := by
  rw [normalizedCuspidalQuotientWeight,norm_smul,quotientWeightNormalization_complex_norm]
  apply (mul_le_mul_of_nonneg_left (cuspidalQuotientWeightEndomorphism_norm N hN hδ hν)
    (quotientWeightNormalization_pos δ).le).trans
  have he : quotientWeightNormalization δ*(quotientWeightBound δ+1)=1 :=
    inv_mul_cancel₀ (by linarith [quotientWeightBound_nonneg δ] : quotientWeightBound δ+1≠0)
  nlinarith [quotientWeightNormalization_pos δ]

theorem quotientWeightNormalization_smul_norm_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (δ : ℝ) (x : E) :
    ‖(quotientWeightNormalization δ:ℂ) • x‖≤‖x‖ := by
  rw [norm_smul,quotientWeightNormalization_complex_norm]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (quotientWeightNormalization_le_one δ)
    (norm_nonneg x)

#print axioms cuspidalQuotientWeight_norm
#print axioms cuspidalQuotientWeightEndomorphism_norm
#print axioms quotientWeightNormalization_pos
#print axioms quotientWeightNormalization_le_one
#print axioms quotientWeightNormalization_complex_norm
#print axioms normalizedCuspidalQuotientWeight_norm
#print axioms quotientWeightNormalization_smul_norm_le

end QuantitativeMaass
