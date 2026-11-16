module

public import QuantitativeMaassExactAtkinReflectionV1
public import QuantitativeMaassNormalizerBandV1
public import QuantitativeMaassPhysicalSectorIdentificationV1
public import QuantitativeArithmeticNewBandProductV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open QuantitativeNinaMaass QuantitativeNewGap AsymptoticSectorSigns
open QuantitativeArithmeticRepeatedTwoBands QuantitativeArithmeticNewBandProjections
namespace QuantitativeMaass

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    NormedAddCommGroup (S.parityBand a b σ) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    InnerProductSpace ℂ (S.parityBand a b σ) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    FiniteDimensional ℂ (S.parityBand a b σ) := by
  let := S.band_finiteDimensional a b
  infer_instance




local instance (N : ℕ) (p : ↥N.primeFactors) : NeZero p.val :=
  ⟨(Nat.prime_of_mem_primeFactors p.property).ne_zero⟩

local instance (N : ℕ) [NeZero N] (p : ↥N.primeFactors) : NeZero (N/p.val) :=
  ⟨(prime_quotient_pos N p.val (NeZero.pos N)
    (Nat.prime_of_mem_primeFactors p.property) (Nat.dvd_of_mem_primeFactors p.property)).ne'⟩

local instance {N : ℕ} [NeZero N] {hN : 0<N}
    (T : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    CompleteSpace (T.parityBand a b σ) := FiniteDimensional.complete ℂ _

local instance {N : ℕ} [NeZero N] {hN : 0<N}
    (T : CuspEnergySpectrum N hN) (a b σ : ℝ)
    (K : Submodule ℂ (T.parityBand a b σ)) : K.HasOrthogonalProjection := by
  let : CompleteSpace K := FiniteDimensional.complete ℂ _
  infer_instance


def normalizerBandPullback {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)
    (g : quotientNormalizerGroup N) (a b : ℝ) : S.band a b →ₗᵢ[ℂ] S.band a b where
  toLinearMap := (cuspidalNormalizerPullback N hN g).toLinearMap.restrict
    (cuspidalNormalizerPullback_band S g a b)
  norm_map' x := (cuspidalNormalizerPullback N hN g).norm_map x.val

def normalizerParityBandPullback {N : ℕ} [NeZero N] {hN : 0<N}
    (S : CuspEnergySpectrum N hN) (g : quotientNormalizerGroup N)
    (hr : ∀ v,quotientNormalizerPullback N g (reflectionIsometry N v)=
      reflectionIsometry N (quotientNormalizerPullback N g v)) (a b σ : ℝ) :
    S.parityBand a b σ →ₗᵢ[ℂ] S.parityBand a b σ where
  toLinearMap := (normalizerBandPullback S g a b).toLinearMap.restrict (by
    rintro v ⟨w,rfl⟩
    refine ⟨normalizerBandPullback S g a b w,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change parityProjection N σ (quotientNormalizerPullback N g w.val.val)=
      quotientNormalizerPullback N g (parityProjection N σ w.val.val)
    simp only [parityProjection_apply,map_smul,map_add,hr])
  norm_map' x := (normalizerBandPullback S g a b).norm_map x.val

theorem normalizerParityBandPullback_apply {N : ℕ} [NeZero N] {hN : 0<N}
    (S : CuspEnergySpectrum N hN) (g : quotientNormalizerGroup N)
    (hr : ∀ v,quotientNormalizerPullback N g (reflectionIsometry N v)=
      reflectionIsometry N (quotientNormalizerPullback N g v))
    (a b σ : ℝ) (x : S.parityBand a b σ) :
    inclusion S a b σ (normalizerParityBandPullback S g hr a b σ x)=
      quotientNormalizerPullback N g (inclusion S a b σ x) := rfl

def sectorNormalizerGroup (N : ℕ) (hN : 0<N) : SectorSignIndex N → quotientNormalizerGroup N
  | none => completedFrickeNormalizer N hN
  | some p => completedLocalAtkinNormalizer N hN p

theorem sectorNormalizerGroup_action (N : ℕ) (hN : 0<N) (i : SectorSignIndex N) :
    (quotientNormalizerPullback N (sectorNormalizerGroup N hN i)).toContinuousLinearMap=
      completedSectorNormalizer N hN i := by cases i <;> rfl

theorem sectorNormalizerGroup_reflection (N : ℕ) (hN : 0<N) (i : SectorSignIndex N)
    (x : AutomorphicSpace N) :
    quotientNormalizerPullback N (sectorNormalizerGroup N hN i) (reflectionIsometry N x)=
      reflectionIsometry N (quotientNormalizerPullback N (sectorNormalizerGroup N hN i) x) := by
  cases i with
  | none => exact frickeIsometry_reflection N hN x
  | some p => exact (DFunLike.congr_fun (completedLocalAtkin_reflection_commute N hN p).eq x).symm

/-- The actual finite normalizer family on a fixed cusp parity band. -/
def sectorParityBandNormalizer {N : ℕ} [NeZero N] {hN : 0<N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (i : SectorSignIndex N) :
    S.parityBand a b σ →ₗᵢ[ℂ] S.parityBand a b σ :=
  normalizerParityBandPullback S (sectorNormalizerGroup N hN i)
    (sectorNormalizerGroup_reflection N hN i) a b σ

theorem sectorParityBandNormalizer_apply {N : ℕ} [NeZero N] {hN : 0<N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (i : SectorSignIndex N)
    (x : S.parityBand a b σ) :
    inclusion S a b σ (sectorParityBandNormalizer S a b σ i x)=
      completedSectorNormalizer N hN i (inclusion S a b σ x) := by
  change quotientNormalizerPullback N (sectorNormalizerGroup N hN i) _=_
  exact DFunLike.congr_fun (sectorNormalizerGroup_action N hN i) _


theorem parityBand_inclusion_injective {N : ℕ} [NeZero N] {hN : 0<N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) : Function.Injective (inclusion S a b σ) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact h

theorem sectorParityBandNormalizer_involutive {N : ℕ} [NeZero N] {hN : 0<N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (i : SectorSignIndex N) :
    Function.Involutive (sectorParityBandNormalizer S a b σ i) := by
  intro x
  apply parityBand_inclusion_injective S a b σ
  rw [sectorParityBandNormalizer_apply,sectorParityBandNormalizer_apply]
  exact completedSectorNormalizer_involutive N hN i _

theorem sectorParityBandNormalizer_selfAdjoint {N : ℕ} [NeZero N] {hN : 0<N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (i : SectorSignIndex N) :
    IsSelfAdjoint (sectorParityBandNormalizer S a b σ i).toContinuousLinearMap := by
  apply LinearMap.IsSymmetric.clm_adjoint_eq
  intro x y
  have hh := (sectorParityBandNormalizer S a b σ i).inner_map_map x
    (sectorParityBandNormalizer S a b σ i y)
  rw [sectorParityBandNormalizer_involutive S a b σ i y] at hh
  exact hh

theorem sectorParityBandNormalizers_commute {N : ℕ} [NeZero N] {hN : 0<N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (i j : SectorSignIndex N) :
    Commute (sectorParityBandNormalizer S a b σ i).toContinuousLinearMap
      (sectorParityBandNormalizer S a b σ j).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  apply parityBand_inclusion_injective S a b σ
  change inclusion S a b σ (sectorParityBandNormalizer S a b σ i (sectorParityBandNormalizer S a b σ j x))=
    inclusion S a b σ (sectorParityBandNormalizer S a b σ j (sectorParityBandNormalizer S a b σ i x))
  simp only [sectorParityBandNormalizer_apply]
  exact DFunLike.congr_fun (completedSectorNormalizers_commute N hN i j).eq _

theorem sectorParityBandNormalizer_new {N : ℕ} [NeZero N] {hN : 0<N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (i : SectorSignIndex N)
    (x : S.parityBand a b σ) (hx : x∈QuantitativeArithmeticNewBandProduct.totalNewBand N hN S a b σ) :
    sectorParityBandNormalizer S a b σ i x∈QuantitativeArithmeticNewBandProduct.totalNewBand N hN S a b σ := by
  change inclusion S a b σ (sectorParityBandNormalizer S a b σ i x)∈newSpace N hN
  rw [sectorParityBandNormalizer_apply]
  exact (completedSectorNormalizer_cuspidalNew N hN i (inclusion S a b σ x)
    ⟨x.val.val.property,hx⟩).2

#print axioms parityBand_inclusion_injective
#print axioms sectorParityBandNormalizer_involutive
#print axioms sectorParityBandNormalizer_selfAdjoint
#print axioms sectorParityBandNormalizers_commute
#print axioms sectorParityBandNormalizer_new
#print axioms normalizerParityBandPullback_apply
#print axioms sectorNormalizerGroup_action
#print axioms sectorNormalizerGroup_reflection
#print axioms sectorParityBandNormalizer_apply
end QuantitativeMaass
