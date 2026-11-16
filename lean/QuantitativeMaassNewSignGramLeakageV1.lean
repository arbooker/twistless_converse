module

public import QuantitativeMaassNewSignBandProjectionV1
public import QuantitativeMaassQuotientWeightBandStepsV1
public import QuantitativeMaassWeightedSubspaceGramV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open QuantitativeNinaMaass

namespace QuantitativeMaass

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    FiniteDimensional ℂ (S.band a b) := S.band_finiteDimensional a b

/-- The genuine normalized new/sign Gram, extended by zero on the
orthogonal complement of its source. -/
def newSignWeightedGram (N : ℕ) [NeZero N] (hN : 0<N)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (χ : admissibleGeneratorIndex N hN → ℂ) :
    localCuspidalSpace N hN →L[ℂ] localCuspidalSpace N hN :=
  (cuspidalNewSignSpace N hN χ).starProjection.comp
    ((normalizedCuspidalQuotientWeight N hN hδ hν).comp (cuspidalNewSignSpace N hN χ).starProjection)

/-- Exact identification with the actual restricted embedding Gram. -/
theorem newSignWeightedGram_actual (N : ℕ) [NeZero N] (hN : 0<N)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (χ : admissibleGeneratorIndex N hN → ℂ) :
    newSignWeightedGram N hN hδ hν χ=
      (cuspidalNewSignSpace N hN χ).subtypeL.comp
        (((normalizedNewSignWeightedEmbedding N hN hδ hν χ).adjoint.comp
          (normalizedNewSignWeightedEmbedding N hN hδ hν χ)).comp
            (cuspidalNewSignSpace N hN χ).orthogonalProjectionOnto) := by
  rw [normalizedNewSignWeightedEmbedding,normalizedWeightedSubspace_gram]
  rfl

theorem newSignWeightedGram_norm (N : ℕ) [NeZero N] (hN : 0<N)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (χ : admissibleGeneratorIndex N hN → ℂ) : ‖newSignWeightedGram N hN hδ hν χ‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  apply ((cuspidalNewSignSpace N hN χ).norm_starProjection_apply_le _).trans
  apply ((normalizedCuspidalQuotientWeight N hN hδ hν).le_of_opNorm_le
    (normalizedCuspidalQuotientWeight_norm N hN hδ hν) _).trans
  simp only [one_mul]
  change ‖(cuspidalNewSignSpace N hN χ).starProjection x‖≤‖x‖
  exact (cuspidalNewSignSpace N hN χ).norm_starProjection_apply_le x

/-- The new/sign restriction has the same nested spectral leakage bound.
Both new/sign projections are genuine and their spectral commutation has
already been proved. -/
theorem newSignWeightedGram_nested_energy {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Fintype ι]
    {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (χ : admissibleGeneratorIndex N hN → ℂ) (v : OrthonormalBasis ι ℂ E)
    (t B L : ℝ) (hL : 0<L) (ht : B+L+2≤t)
    (T : E →L[ℂ] S.band (t-B) (t+B)) :
    (∑ i,‖newSignWeightedGram N hN hδ hν χ (T (v i)).val-
      (S.band (t-(B+L+2)) (t+(B+L+2))).starProjection
        (newSignWeightedGram N hN hδ hν χ (T (v i)).val)‖^2)≤
      ‖T‖^2*(16*(4*quotientWeightBound δ*(2*ν:ℝ))^2*
        (Module.finrank ℂ (S.band (t-B) (t+B)):ℝ)/L^2) := by
  let Q := (cuspidalNewSignSpace N hN χ).starProjection
  let A := normalizedCuspidalQuotientWeight N hN hδ hν
  let V := S.band (t-(B+L+2)) (t+(B+L+2))
  let T' : E →L[ℂ] S.band (t-B) (t+B) :=
    (Q.comp ((S.band (t-B) (t+B)).subtypeL.comp T)).codRestrict _
      (fun x => cuspidalNewSignProjection_band S χ _ _ (T x).val (T x).property)
  have hn : ‖T'‖≤‖T‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
    intro x
    change ‖Q (T x).val‖≤‖T‖*‖x‖
    exact ((cuspidalNewSignSpace N hN χ).norm_starProjection_apply_le _).trans (T.le_opNorm x)
  have he (i : ι) : newSignWeightedGram N hN hδ hν χ (T (v i)).val-
      V.starProjection (newSignWeightedGram N hN hδ hν χ (T (v i)).val)=
        Q (A (T' (v i)).val-(quotientWeightBandStep S hδ hν t B L (T' (v i))).val) := by
    have hc := DFunLike.congr_fun
      (cuspidalNewSignProjection_band_commute S χ (t-(B+L+2)) (t+(B+L+2)))
        (A (Q (T (v i)).val))
    change Q (A (Q (T (v i)).val))-V.starProjection (Q (A (Q (T (v i)).val)))=
      Q (A (Q (T (v i)).val)-V.starProjection (A (Q (T (v i)).val)))
    rw [map_sub]
    exact congrArg (fun y => Q (A (Q (T (v i)).val))-y) hc
  have hsum : (∑ i,‖newSignWeightedGram N hN hδ hν χ (T (v i)).val-
      V.starProjection (newSignWeightedGram N hN hδ hν χ (T (v i)).val)‖^2)≤
        ∑ i,‖A (T' (v i)).val-(quotientWeightBandStep S hδ hν t B L (T' (v i))).val‖^2 := by
    apply Finset.sum_le_sum
    intro i _
    rw [he i]
    exact pow_le_pow_left₀ (norm_nonneg _)
      ((cuspidalNewSignSpace N hN χ).norm_starProjection_apply_le _) 2
  apply hsum.trans
  apply (quotientWeightBandStep_defect_energy S hδ hν v t B L hL ht T').trans
  have hn2 : ‖T'‖^2≤‖T‖^2 := by nlinarith [norm_nonneg T',norm_nonneg T]
  exact mul_le_mul_of_nonneg_right hn2 (by positivity)

#print axioms newSignWeightedGram_actual
#print axioms newSignWeightedGram_norm
#print axioms newSignWeightedGram_nested_energy

end QuantitativeMaass
