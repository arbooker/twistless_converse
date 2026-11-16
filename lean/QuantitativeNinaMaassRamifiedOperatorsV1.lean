module

public import QuantitativeNinaMaassPrimeOldV1
public import QuantitativeNinaMaassRamifiedCoefficientsV1
public import QuantitativeNinaMaassNewResolventV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory QuantitativeMaass
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology InnerProductSpace

/-!
The actual local normalizer on each finite new-parity band. Its preservation,
symmetry and commutation with the spectral resolvent and global Fricke are
inherited from the proved physical operators. The literal upper-branch
operator is identified with its negative p^(-1/2) multiple on the newspace.
-/

namespace QuantitativeNinaMaass

theorem newSpace_prime_trace (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hM : 0 < M) (v : AutomorphicSpace (p * M))
    (hv : v ∈ newSpace (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM)) :
    v ∈ newTraceKernel (Nat.mul_pos (Fact.out : p.Prime).pos hM) (Nat.dvd_mul_left M p) := by
  simp only [newSpace, Submodule.mem_iInf] at hv
  have h := hv ⟨p, Fact.out, Nat.dvd_mul_right p M⟩
  simpa only [Nat.mul_div_cancel_left M (Fact.out : p.Prime).pos] using h

theorem normalizedUpperBranches_eq_normalizer (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hM : 0 < M) (hpM : ¬ p ∣ M) (A B : ℤ)
    (hAB : (p : ℤ) * A + (M : ℤ) * B = 1)
    (f : AutomorphicL2.representatives (gamma (p * M)) (quotientMeasure (p * M)))
    (hf : Continuous f.val)
    (hv : AutomorphicL2.denseEmbedding _ _ f ∈
      newSpace (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM)) :
    normalizedUpperBranches p (Fact.out : p.Prime).pos f.val =
      fun z => (-((Real.sqrt (p : ℝ) : ℂ)⁻¹)) *
        (primeNormalizerRepresentative M p hM A B hAB f).val z := by
  have htrace := newSpace_prime_trace M p hM _ hv
  have hsecond := continuous_new_dilation_trace_zero M p hM (Fact.out : p.Prime).pos f hf htrace
  funext z
  unfold normalizedUpperBranches
  rw [upperBranchSum_simple_eq_neg_local M p hM hpM A B hAB f.val
    (representative_matrix_invariant (p * M) f) hsecond,
    primeNormalizerRepresentative_local, Complex.ofReal_inv]
  ring

namespace CuspEnergySpectrum

local instance (N : ℕ) (hN : 0 < N) : NormedAddCommGroup (localCuspidalSpace N hN) :=
  inferInstance
local instance (N : ℕ) (hN : 0 < N) : InnerProductSpace ℂ (localCuspidalSpace N hN) :=
  inferInstance
local instance {N : ℕ} {hN : 0 < N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0 < N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    NormedAddCommGroup (S.parityBand a b σ) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    InnerProductSpace ℂ (S.parityBand a b σ) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (P : Set ℕ) :
    NormedAddCommGroup (S.partialParityBand a b σ P) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (P : Set ℕ) :
    InnerProductSpace ℂ (S.partialParityBand a b σ P) := inferInstance

def primeNormalizerParityBandMap (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hM : 0 < M) (S : CuspEnergySpectrum (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1) (a b σ : ℝ) :
    S.parityBand a b σ →ₗ[ℂ] S.parityBand a b σ :=
  S.parityBandMap S (HeckeL2.normalizer M p hM A B hAB).toContinuousLinearMap
    (primeNormalizer_mem_cuspidal M p hM A B hAB)
    (fun _ _ h => primeNormalizer_friedrichsGraph M p hM A B hAB h)
    (primeNormalizer_reflection M p hM A B hAB) a b σ

def newPrimeNormalizer (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hM : 0 < M) (S : CuspEnergySpectrum (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1) (a b σ : ℝ) :
    S.partialParityBand a b σ univ →ₗ[ℂ] S.partialParityBand a b σ univ :=
  (primeNormalizerParityBandMap M p hM S A B hAB a b σ).restrict (by
    intro v hv
    rw [mem_partialParityBand, partialNewSpace_univ] at hv ⊢
    exact primeNormalizer_mem_newSpace M p hM A B hAB _ hv)

theorem newPrimeNormalizer_actual (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hM : 0 < M) (S : CuspEnergySpectrum (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1) (a b σ : ℝ)
    (v : S.partialParityBand a b σ univ) :
    ((newPrimeNormalizer M p hM S A B hAB a b σ v).val.val.val : AutomorphicSpace (p * M)) =
      HeckeL2.normalizer M p hM A B hAB (v.val.val.val : AutomorphicSpace (p * M)) := rfl

theorem newPrimeNormalizer_symmetric (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hM : 0 < M) (S : CuspEnergySpectrum (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1) (a b σ : ℝ) :
    (newPrimeNormalizer M p hM S A B hAB a b σ).IsSymmetric := by
  intro v w
  exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (HeckeL2.normalizer_selfAdjoint M p hM A B hAB)
      (v.val.val.val : AutomorphicSpace (p * M)) (w.val.val.val : AutomorphicSpace (p * M))

theorem newPrimeNormalizer_resolvent (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hM : 0 < M) (S : CuspEnergySpectrum (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1) (a b σ : ℝ) :
    Commute (newPrimeNormalizer M p hM S A B hAB a b σ)
      (S.partialNewResolvent a b σ univ) := by
  apply LinearMap.ext
  intro v
  exact Subtype.ext (Subtype.ext (Subtype.ext (Subtype.ext
    (primeNormalizer_resolvent M p hM A B hAB (v.val.val.val : AutomorphicSpace (p * M))).symm)))

theorem newPrimeNormalizer_fricke (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hM : 0 < M) (S : CuspEnergySpectrum (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1) (a b σ : ℝ) :
    Commute (newPrimeNormalizer M p hM S A B hAB a b σ)
      (S.partialNewFricke a b σ univ) := by
  apply LinearMap.ext
  intro v
  exact Subtype.ext (Subtype.ext (Subtype.ext (Subtype.ext
    (primeNormalizer_fricke M p hM A B hAB (v.val.val.val : AutomorphicSpace (p * M))))))

theorem newPrimeNormalizer_involutive (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hM : 0 < M) (S : CuspEnergySpectrum (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1) (a b σ : ℝ) :
    Function.Involutive (newPrimeNormalizer M p hM S A B hAB a b σ) := by
  intro v
  exact Subtype.ext (Subtype.ext (Subtype.ext (Subtype.ext
    (primeNormalizer_involutive M p hM A B hAB (v.val.val.val : AutomorphicSpace (p * M))))))

/-- The actual simple-ramified correspondence as an endomorphism of the
same finite new-parity space. Its literal upper-branch action is proved below. -/
def newRamifiedOperator (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hM : 0 < M) (S : CuspEnergySpectrum (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1) (a b σ : ℝ) :
    S.partialParityBand a b σ univ →ₗ[ℂ] S.partialParityBand a b σ univ :=
  (-((Real.sqrt (p : ℝ) : ℂ)⁻¹)) • newPrimeNormalizer M p hM S A B hAB a b σ

theorem newRamifiedOperator_representative (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hM : 0 < M) (S : CuspEnergySpectrum (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (hpM : ¬ p ∣ M) (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1)
    (a b σ : ℝ) (v : S.partialParityBand a b σ univ)
    (f g : AutomorphicL2.representatives (gamma (p * M)) (quotientMeasure (p * M)))
    (hf : Continuous f.val) (hg : Continuous g.val)
    (hef : AutomorphicL2.denseEmbedding _ _ f = (v.val.val.val : AutomorphicSpace (p * M)))
    (heg : AutomorphicL2.denseEmbedding _ _ g =
      ((newRamifiedOperator M p hM S A B hAB a b σ v).val.val.val : AutomorphicSpace (p * M))) :
    g.val = normalizedUpperBranches p (Fact.out : p.Prime).pos f.val := by
  have hv : AutomorphicL2.denseEmbedding _ _ f ∈
      newSpace (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM) := by
    rw [hef]
    have h := v.property
    rwa [mem_partialParityBand, partialNewSpace_univ] at h
  have he : g = (-((Real.sqrt (p : ℝ) : ℂ)⁻¹)) •
      primeNormalizerRepresentative M p hM A B hAB f := by
    apply continuous_representative_unique (p * M) _ _ hg
      (continuous_const.mul (primeNormalizerRepresentative_continuous M p hM A B hAB f hf))
    rw [map_smul, ← primeNormalizer_apply, hef, heg]
    rfl
  rw [he, normalizedUpperBranches_eq_normalizer M p hM hpM A B hAB f hf hv]
  rfl

theorem newRamifiedOperator_symmetric (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hM : 0 < M) (S : CuspEnergySpectrum (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1) (a b σ : ℝ) :
    (newRamifiedOperator M p hM S A B hAB a b σ).IsSymmetric := by
  intro v w
  have hc : (starRingEnd ℂ) (-((Real.sqrt (p : ℝ) : ℂ)⁻¹)) =
      -((Real.sqrt (p : ℝ) : ℂ)⁻¹) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_neg, Complex.conj_ofReal]
  simp only [newRamifiedOperator, LinearMap.smul_apply,
    inner_smul_left (𝕜 := ℂ), inner_smul_right (𝕜 := ℂ), hc,
    newPrimeNormalizer_symmetric M p hM S A B hAB a b σ v w]

theorem newRamifiedOperator_resolvent (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hM : 0 < M) (S : CuspEnergySpectrum (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1) (a b σ : ℝ) :
    Commute (newRamifiedOperator M p hM S A B hAB a b σ)
      (S.partialNewResolvent a b σ univ) := by
  exact (newPrimeNormalizer_resolvent M p hM S A B hAB a b σ).smul_left
    (-((Real.sqrt (p : ℝ) : ℂ)⁻¹))

theorem newRamifiedOperator_fricke (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hM : 0 < M) (S : CuspEnergySpectrum (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1) (a b σ : ℝ) :
    Commute (newRamifiedOperator M p hM S A B hAB a b σ)
      (S.partialNewFricke a b σ univ) := by
  exact (newPrimeNormalizer_fricke M p hM S A B hAB a b σ).smul_left
    (-((Real.sqrt (p : ℝ) : ℂ)⁻¹))

/-- This records a constructed operator on the actual finite newspace.
The literal upper-branch action is part of the verification of the object;
existence is proved from the physical normalizer and trace identities below. -/
structure RamifiedBandOperator {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (p : ℕ) (hp : p.Prime) where
  operator : S.partialParityBand a b σ univ →ₗ[ℂ] S.partialParityBand a b σ univ
  symmetric : operator.IsSymmetric
  resolvent_commute : Commute operator (S.partialNewResolvent a b σ univ)
  fricke_commute : Commute operator (S.partialNewFricke a b σ univ)
  representative : ∀ (v : S.partialParityBand a b σ univ)
    (f g : AutomorphicL2.representatives (gamma N) (quotientMeasure N)),
    Continuous f.val → Continuous g.val →
    AutomorphicL2.denseEmbedding _ _ f = (v.val.val.val : AutomorphicSpace N) →
    AutomorphicL2.denseEmbedding _ _ g = ((operator v).val.val.val : AutomorphicSpace N) →
    g.val = normalizedUpperBranches p hp.pos f.val

/-- Every ramified prime has a genuine symmetric operator on the same
new-parity band. It is zero at square divisors and a scaled actual local
normalizer at simple divisors. No newspace invariance is assumed. -/
theorem exists_ramifiedBandOperator {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (p : ℕ) (hp : p.Prime) (hpN : p ∣ N) :
    Nonempty (S.RamifiedBandOperator a b σ p hp) := by
  obtain ⟨M, rfl⟩ := hpN
  have hM : 0 < M := by
    by_contra h
    have hz : M = 0 := by omega
    simp [hz] at hN
  let : NeZero M := ⟨hM.ne'⟩
  let : Fact p.Prime := ⟨hp⟩
  by_cases hpM : p ∣ M
  · refine ⟨{ operator := 0
              symmetric := by intro v w; simp
              resolvent_commute := by change (0 : Module.End ℂ _) * _ = _ * 0; simp
              fricke_commute := by change (0 : Module.End ℂ _) * _ = _ * 0; simp
              representative := ?_ }⟩
    intro v f g hf hg hef heg
    have hv : AutomorphicL2.denseEmbedding _ _ f ∈ newSpace (p * M) hN := by
      rw [hef]
      have h := v.property
      rwa [mem_partialParityBand, partialNewSpace_univ] at h
    have hg0 : g = 0 := by
      apply continuous_representative_unique (p * M) g 0 hg continuous_const
      rw [map_zero, heg]
      rfl
    rw [hg0, normalizedUpperBranches_repeated_zero M p hM hp hpM f hf
      (newSpace_prime_trace M p hM _ hv)]
    rfl
  · have hc : p.Coprime M := hp.coprime_iff_not_dvd.mpr hpM
    have hAB : (p : ℤ) * Nat.gcdA p M + (M : ℤ) * Nat.gcdB p M = 1 := by
      have h := Nat.gcd_eq_gcd_ab p M
      rw [hc.gcd_eq_one, Nat.cast_one] at h
      exact h.symm
    exact ⟨{
      operator := newRamifiedOperator M p hM S _ _ hAB a b σ
      symmetric := newRamifiedOperator_symmetric M p hM S _ _ hAB a b σ
      resolvent_commute := newRamifiedOperator_resolvent M p hM S _ _ hAB a b σ
      fricke_commute := newRamifiedOperator_fricke M p hM S _ _ hAB a b σ
      representative := newRamifiedOperator_representative M p hM S hpM _ _ hAB a b σ }⟩

#print axioms newPrimeNormalizer_actual
#print axioms newPrimeNormalizer_symmetric
#print axioms newPrimeNormalizer_resolvent
#print axioms newPrimeNormalizer_fricke
#print axioms newPrimeNormalizer_involutive
#print axioms newRamifiedOperator_representative
#print axioms newRamifiedOperator_symmetric
#print axioms newRamifiedOperator_resolvent
#print axioms newRamifiedOperator_fricke
#print axioms exists_ramifiedBandOperator

end CuspEnergySpectrum

#print axioms newSpace_prime_trace
#print axioms normalizedUpperBranches_eq_normalizer

end QuantitativeNinaMaass
