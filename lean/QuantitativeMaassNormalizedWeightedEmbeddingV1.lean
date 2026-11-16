module

public import QuantitativeMaassQuotientWeightContractionV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory AsymptoticClassicalPetersson
open scoped InnerProductSpace

namespace QuantitativeMaass

/-- The positive real square-root scaling has exactly the prescribed Gram. -/
theorem gram_sqrt_scaling {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (R : E →L[ℂ] F) {q : ℝ} (hq : 0≤q) :
    ((Real.sqrt q:ℂ) • R).adjoint.comp ((Real.sqrt q:ℂ) • R)=
      (q:ℂ) • (R.adjoint.comp R) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right,
    smul_apply,inner_smul_right,inner_smul_left]
  rw [Complex.conj_ofReal,←mul_assoc,←Complex.ofReal_mul,←pow_two,Real.sq_sqrt hq]

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance

def normalizedCuspidalWeightedEmbedding (N : ℕ) (hN : 0<N)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) :
    localCuspidalSpace N hN →L[ℂ] Lp ℂ 2 (quotientMeasure 0) :=
  (Real.sqrt (quotientWeightNormalization δ):ℂ) •
    ((weightedQuotientEmbedding N hδ hν).comp (localCuspidalSpace N hN).subtypeL)

/-- The normalized actual cylinder embedding has exactly the contraction
used in the spectral leakage and polynomial comparison theorems. -/
theorem normalizedCuspidalWeightedEmbedding_gram (N : ℕ) (hN : 0<N)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) :
    (normalizedCuspidalWeightedEmbedding N hN hδ hν).adjoint.comp
      (normalizedCuspidalWeightedEmbedding N hN hδ hν)=
        normalizedCuspidalQuotientWeight N hN hδ hν := by
  rw [normalizedCuspidalWeightedEmbedding,gram_sqrt_scaling _ (quotientWeightNormalization_pos δ).le,
    weightedQuotientEmbedding_cuspidal_gram]
  rfl

theorem normalizedCuspidalWeightedEmbedding_norm (N : ℕ) (hN : 0<N)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) :
    ‖normalizedCuspidalWeightedEmbedding N hN hδ hν‖≤1 := by
  have hh := ContinuousLinearMap.norm_adjoint_comp_self (normalizedCuspidalWeightedEmbedding N hN hδ hν)
  rw [normalizedCuspidalWeightedEmbedding_gram] at hh
  have hn := normalizedCuspidalQuotientWeight_norm N hN hδ hν
  nlinarith [norm_nonneg (normalizedCuspidalWeightedEmbedding N hN hδ hν)]

/-- Restricting the actual normalized embedding introduces precisely the
adjoint inclusion on the left of its Gram. -/
theorem normalizedCuspidalWeightedEmbedding_restricted_gram {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (N : ℕ) (hN : 0<N) {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (J : E →L[ℂ] localCuspidalSpace N hN) :
    ((normalizedCuspidalWeightedEmbedding N hN hδ hν).comp J).adjoint.comp
      ((normalizedCuspidalWeightedEmbedding N hN hδ hν).comp J)=
        J.adjoint.comp ((normalizedCuspidalQuotientWeight N hN hδ hν).comp J) := by
  rw [ContinuousLinearMap.adjoint_comp]
  have hg := normalizedCuspidalWeightedEmbedding_gram N hN hδ hν
  apply ContinuousLinearMap.ext
  intro x
  have hh := DFunLike.congr_fun hg (J x)
  exact congrArg J.adjoint hh

#print axioms gram_sqrt_scaling
#print axioms normalizedCuspidalWeightedEmbedding_gram
#print axioms normalizedCuspidalWeightedEmbedding_norm
#print axioms normalizedCuspidalWeightedEmbedding_restricted_gram

end QuantitativeMaass
