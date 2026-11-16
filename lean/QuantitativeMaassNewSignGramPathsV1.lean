module

public import QuantitativeMaassNewSignGramLeakageV1
public import QuantitativeMaassQuotientWeightFixedBandV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open QuantitativeNinaMaass

namespace QuantitativeMaass
open Weighted (cutoffWordRadius cutoffWordBand)

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance

def newSignGramBandStep {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (χ : admissibleGeneratorIndex N hN → ℂ) (t B L : ℝ) :
    S.band (t-B) (t+B) →L[ℂ] S.band (t-(B+L+2)) (t+(B+L+2)) :=
  let V := S.band (t-(B+L+2)) (t+(B+L+2))
  let : FiniteDimensional ℂ V := S.band_finiteDimensional _ _
  V.orthogonalProjectionOnto.comp
    ((newSignWeightedGram N hN hδ hν χ).comp (S.band (t-B) (t+B)).subtypeL)

theorem newSignGramBandStep_norm {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (χ : admissibleGeneratorIndex N hN → ℂ) (t B L : ℝ) :
    ‖newSignGramBandStep S hδ hν χ t B L‖≤1 := by
  let V := S.band (t-(B+L+2)) (t+(B+L+2))
  let : FiniteDimensional ℂ V := S.band_finiteDimensional _ _
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  apply (V.norm_orthogonalProjectionOnto_apply_le _).trans
  exact (newSignWeightedGram N hN hδ hν χ).le_of_opNorm_le
    (newSignWeightedGram_norm N hN hδ hν χ) x.val

theorem newSignGramBandStep_defect_energy {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Fintype ι]
    {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (χ : admissibleGeneratorIndex N hN → ℂ)
    (v : OrthonormalBasis ι ℂ E) (t B L : ℝ) (hL : 0<L) (ht : B+L+2≤t)
    (T : E →L[ℂ] S.band (t-B) (t+B)) :
    (∑ i,‖newSignWeightedGram N hN hδ hν χ (T (v i)).val-
      (newSignGramBandStep S hδ hν χ t B L (T (v i))).val‖^2)≤
      ‖T‖^2*(16*(4*quotientWeightBound δ*(2*ν:ℝ))^2*
        (Module.finrank ℂ (S.band (t-B) (t+B)):ℝ)/L^2) :=
  newSignWeightedGram_nested_energy S hδ hν χ v t B L hL ht T

/-- Successive spectral compressions of the normalized literal cuspidal Gram. -/
def newSignGramBandPath {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (χ : admissibleGeneratorIndex N hN → ℂ) (t L : ℝ) :
    (n : ℕ) → cutoffWordBand S t L 0 →L[ℂ] cutoffWordBand S t L n
  | 0 => ContinuousLinearMap.id ℂ _
  | n+1 => (newSignGramBandStep S hδ hν χ t (cutoffWordRadius L n) L).comp
      (newSignGramBandPath S hδ hν χ t L n)

/-- The same normalized Gram word without the intermediate band projections.
The cuspidal projection remains part of every factor. -/
def newSignGramAmbientPath {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (χ : admissibleGeneratorIndex N hN → ℂ) (t L : ℝ) :
    ℕ → cutoffWordBand S t L 0 →L[ℂ] localCuspidalSpace N hN
  | 0 => (cutoffWordBand S t L 0).subtypeL
  | n+1 => (newSignWeightedGram N hN hδ hν χ).comp (newSignGramAmbientPath S hδ hν χ t L n)

def newSignGramBandPathAmbient {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (χ : admissibleGeneratorIndex N hN → ℂ) (t L : ℝ) (n : ℕ) :
    cutoffWordBand S t L 0 →L[ℂ] localCuspidalSpace N hN :=
  (cutoffWordBand S t L n).subtypeL.comp (newSignGramBandPath S hδ hν χ t L n)

theorem newSignGramBandPath_norm {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (χ : admissibleGeneratorIndex N hN → ℂ) (t L : ℝ) (n : ℕ) :
    ‖newSignGramBandPath S hδ hν χ t L n‖≤1 := by
  induction n with
  | zero => exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
    have hs := newSignGramBandStep_norm S hδ hν χ t (cutoffWordRadius L n) L
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    nlinarith [norm_nonneg (newSignGramBandStep S hδ hν χ t (cutoffWordRadius L n) L),
      norm_nonneg (newSignGramBandPath S hδ hν χ t L n)]

theorem newSignGramBandPath_defect_energy {ι : Type*} [Fintype ι]
    {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (χ : admissibleGeneratorIndex N hN → ℂ) (t L : ℝ) (hL : 0<L)
    (v : OrthonormalBasis ι ℂ (cutoffWordBand S t L 0)) (n : ℕ)
    (ht : cutoffWordRadius L n+L+2≤t) :
    finiteSourceEnergy v ((newSignWeightedGram N hN hδ hν χ).comp
      (newSignGramBandPathAmbient S hδ hν χ t L n)-newSignGramBandPathAmbient S hδ hν χ t L (n+1))≤
      16*(4*quotientWeightBound δ*(2*ν:ℝ))^2*
        (Module.finrank ℂ (cutoffWordBand S t L n):ℝ)/L^2 := by
  let : FiniteDimensional ℂ (cutoffWordBand S t L 0) := S.band_finiteDimensional _ _
  have hh := newSignGramBandStep_defect_energy S hδ hν χ v t (cutoffWordRadius L n)
    L hL ht (newSignGramBandPath S hδ hν χ t L n)
  have hn : ‖newSignGramBandPath S hδ hν χ t L n‖^2≤1 := by
    nlinarith [newSignGramBandPath_norm S hδ hν χ t L n,norm_nonneg (newSignGramBandPath S hδ hν χ t L n)]
  have he := hh.trans (mul_le_mul_of_nonneg_right hn (by positivity))
  simp only [one_mul] at he
  exact he

/-- The actual normalized Gram word is close to its successive spectral
compressions, with an explicit sum of defects and no invariant-band premise. -/
theorem newSignGram_word_energy {ι : Type*} [Fintype ι]
    {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (χ : admissibleGeneratorIndex N hN → ℂ) (t L : ℝ) (hL : 0<L)
    (v : OrthonormalBasis ι ℂ (cutoffWordBand S t L 0)) (n : ℕ)
    (ht : ∀ j<n,cutoffWordRadius L j+L+2≤t) :
    finiteSourceEnergy v (newSignGramAmbientPath S hδ hν χ t L n-
      newSignGramBandPathAmbient S hδ hν χ t L n)≤
      (2:ℝ)^n*∑ j∈Finset.range n,
        16*(4*quotientWeightBound δ*(2*ν:ℝ))^2*
          (Module.finrank ℂ (cutoffWordBand S t L j):ℝ)/L^2 := by
  have hh := recursive_leakage_energy v (fun _ => newSignWeightedGram N hN hδ hν χ)
    (newSignGramAmbientPath S hδ hν χ t L) (newSignGramBandPathAmbient S hδ hν χ t L)
    (fun _ => newSignWeightedGram_norm N hN hδ hν χ)
    (by ext; rfl) (fun _ => rfl) n
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro j hj
  exact newSignGramBandPath_defect_energy S hδ hν χ t L hL v j (ht j (Finset.mem_range.mp hj))

/-- Repeated compression to one fixed outer band, as required by polynomial
functional calculus on the restricted Gram. -/
def newSignGramFixedPath {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (χ : admissibleGeneratorIndex N hN → ℂ) (t L B : ℝ) :
    ℕ → cutoffWordBand S t L 0 →L[ℂ] localCuspidalSpace N hN
  | 0 => (cutoffWordBand S t L 0).subtypeL
  | n+1 => ((quotientWeightOuterProjection S t B).comp
      (newSignWeightedGram N hN hδ hν χ)).comp
        (newSignGramFixedPath S hδ hν χ t L B n)

theorem newSignGramFixedPath_norm {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (χ : admissibleGeneratorIndex N hN → ℂ) (t L B : ℝ) (n : ℕ) :
    ‖newSignGramFixedPath S hδ hν χ t L B n‖≤1 := by
  induction n with
  | zero =>
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖x.val‖≤1*‖x‖
    simp
  | succ n ih =>
    have ha := newSignWeightedGram_norm N hN hδ hν χ
    have hp := quotientWeightOuterProjection_norm S t B
    have hpa : ‖(quotientWeightOuterProjection S t B).comp
        (newSignWeightedGram N hN hδ hν χ)‖≤1 := by
      apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
      nlinarith [norm_nonneg (quotientWeightOuterProjection S t B),
        norm_nonneg (newSignWeightedGram N hN hδ hν χ)]
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    nlinarith [norm_nonneg ((quotientWeightOuterProjection S t B).comp
      (newSignWeightedGram N hN hδ hν χ)),
      norm_nonneg (newSignGramFixedPath S hδ hν χ t L B n)]

theorem newSignGramOuterProjection_fixes_path {N : ℕ} [NeZero N] {hN : 0<N}
    (S : CuspEnergySpectrum N hN) {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (χ : admissibleGeneratorIndex N hN → ℂ)
    (t L B : ℝ) (j : ℕ) (hj : cutoffWordRadius L j≤B) :
    (quotientWeightOuterProjection S t B).comp
      (newSignGramBandPathAmbient S hδ hν χ t L j)=
        newSignGramBandPathAmbient S hδ hν χ t L j := by
  let : FiniteDimensional ℂ (S.band (t-B) (t+B)) := S.band_finiteDimensional _ _
  apply ContinuousLinearMap.ext
  intro x
  change (S.band (t-B) (t+B)).starProjection
    (newSignGramBandPathAmbient S hδ hν χ t L j x)=newSignGramBandPathAmbient S hδ hν χ t L j x
  apply (S.band (t-B) (t+B)).starProjection_eq_self_iff.mpr
  exact cuspEnergyBand_mono S (by linarith) (by linarith)
    (newSignGramBandPath S hδ hν χ t L j x).property

/-- Energy comparison with one fixed outer spectral band. -/
theorem newSignGram_fixed_energy {ι : Type*} [Fintype ι]
    {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (χ : admissibleGeneratorIndex N hN → ℂ) (t L B : ℝ) (hL : 0<L)
    (v : OrthonormalBasis ι ℂ (cutoffWordBand S t L 0)) (n : ℕ)
    (hB : cutoffWordRadius L n≤B)
    (ht : ∀ j<n,cutoffWordRadius L j+L+2≤t) :
    finiteSourceEnergy v (newSignGramAmbientPath S hδ hν χ t L n-
      newSignGramFixedPath S hδ hν χ t L B n)≤
      4*(2:ℝ)^n*∑ j∈Finset.range n,
        16*(4*quotientWeightBound δ*(2*ν:ℝ))^2*
          (Module.finrank ℂ (cutoffWordBand S t L j):ℝ)/L^2 := by
  have hh := fixed_compression_energy v (fun _ => newSignWeightedGram N hN hδ hν χ)
    (quotientWeightOuterProjection S t B) (newSignGramAmbientPath S hδ hν χ t L)
    (newSignGramBandPathAmbient S hδ hν χ t L) (newSignGramFixedPath S hδ hν χ t L B)
    (fun _ => newSignWeightedGram_norm N hN hδ hν χ)
    (quotientWeightOuterProjection_norm S t B) (by ext; rfl) (by ext; rfl)
    (fun _ => rfl) (fun _ => rfl) n (fun j hj =>
      newSignGramOuterProjection_fixes_path S hδ hν χ t L B j
        ((Weighted.cutoffWordRadius_mono hL.le hj).trans hB))
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro j hj
  exact newSignGramBandPath_defect_energy S hδ hν χ t L hL v j (ht j (Finset.mem_range.mp hj))

#print axioms newSignGramBandStep_norm
#print axioms newSignGramBandStep_defect_energy
#print axioms newSignGramBandPath_norm
#print axioms newSignGramBandPath_defect_energy
#print axioms newSignGram_word_energy
#print axioms newSignGramFixedPath_norm
#print axioms newSignGramOuterProjection_fixes_path
#print axioms newSignGram_fixed_energy

end QuantitativeMaass
