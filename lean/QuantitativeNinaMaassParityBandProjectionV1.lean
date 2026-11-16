module

public import QuantitativeNinaMaassNewParityEnergyBandsV1
public import QuantitativeMaassSectorParityBandProjectionV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set QuantitativeMaass AsymptoticSectorSigns
open QuantitativeArithmeticRepeatedTwoBands
open scoped InnerProductSpace ContDiff SchwartzMap

namespace QuantitativeNinaMaass

local instance (N : ℕ) (hN : 0 < N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0 < N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} {hN : 0 < N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0 < N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0 < N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    FiniteDimensional ℂ (S.band a b) := S.band_finiteDimensional a b
local instance {N : ℕ} [NeZero N] {hN : 0 < N} (S : CuspEnergySpectrum N hN) (a b η : ℝ) :
    NormedAddCommGroup (S.parityBand a b η) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0 < N} (S : CuspEnergySpectrum N hN) (a b η : ℝ) :
    InnerProductSpace ℂ (S.parityBand a b η) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0 < N} (S : CuspEnergySpectrum N hN) (a b η : ℝ) :
    FiniteDimensional ℂ (S.parityBand a b η) := by
  let := S.band_finiteDimensional a b
  infer_instance

local instance {N : ℕ} [NeZero N] {hN : 0<N}
    (S : CuspEnergySpectrum N hN) (a b η : ℝ) :
    CompleteSpace (S.parityBand a b η) := FiniteDimensional.complete ℂ _
local instance {N : ℕ} [NeZero N] {hN : 0<N}
    (S : CuspEnergySpectrum N hN) (a b η : ℝ) (K : Submodule ℂ (S.parityBand a b η)) :
    CompleteSpace K := FiniteDimensional.complete ℂ _
local instance {N : ℕ} [NeZero N] {hN : 0<N}
    (S : CuspEnergySpectrum N hN) (a b η : ℝ) (K : Submodule ℂ (S.parityBand a b η)) :
    K.HasOrthogonalProjection := by
  let : CompleteSpace K := FiniteDimensional.complete ℂ _
  infer_instance

/-- The original completed new/sign/parity space, viewed inside cusp space. -/
def cuspidalNewSignParitySpace (N : ℕ) [NeZero N] (hN : 0 < N)
    (χ : admissibleGeneratorIndex N hN → ℂ) (η : ℝ) :
    Submodule ℂ (localCuspidalSpace N hN) :=
  (completedNewSignParitySpace N hN χ η).comap (localCuspidalSpace N hN).subtype

theorem cuspidalNewSignParitySpace_closed (N : ℕ) [NeZero N] (hN : 0 < N)
    (χ : admissibleGeneratorIndex N hN → ℂ) (η : ℝ) :
    IsClosed (cuspidalNewSignParitySpace N hN χ η : Set (localCuspidalSpace N hN)) :=
  ((completedNewSignSpace_closed N hN χ).inter (completedParitySpace_closed N η)).preimage
    (localCuspidalSpace N hN).subtypeL.continuous

instance cuspidalNewSignParitySpace_complete (N : ℕ) [NeZero N] (hN : 0 < N)
    (χ : admissibleGeneratorIndex N hN → ℂ) (η : ℝ) :
    CompleteSpace (cuspidalNewSignParitySpace N hN χ η) :=
  (cuspidalNewSignParitySpace_closed N hN χ η).completeSpace_coe

/-- The genuine packets preserve both actual source conditions. This
proves unsmoothed wave commutation rather than assuming band invariance. -/
theorem completedNewSignParityProjection_wave (N : ℕ) [NeZero N] (hN : 0 < N)
    (χ : admissibleGeneratorIndex N hN → ℂ) (η t : ℝ) :
    Commute (completedNewSignParitySpace N hN χ η).starProjection
      (Wave.shiftedQuotientWave N t) := by
  apply timePacket_commuting_wave N _ _ t
  intro f hf he hc hr R hR hs
  apply invariantSpace_projection_commute
  · exact Wave.shiftedQuotientWavePacket_isSelfAdjoint N f _ hr
  · intro x hx
    exact ⟨completedNewSignSpace_timePacket N hN χ f hf he hc hr R hR hs x hx.1,
      completedParitySpace_timePacket N η (hc.toSchwartzMap hf) hc he hr R hR hs x hx.2⟩

theorem cuspidalNewSignParityProjection_coe (N : ℕ) [NeZero N] (hN : 0 < N)
    (χ : admissibleGeneratorIndex N hN → ℂ) (η : ℝ) (x : localCuspidalSpace N hN) :
    ((cuspidalNewSignParitySpace N hN χ η).starProjection x).val =
      (completedNewSignParitySpace N hN χ η).starProjection x.val := by
  let y : localCuspidalSpace N hN :=
    ⟨(completedNewSignParitySpace N hN χ η).starProjection x.val,
      ((completedNewSignParitySpace N hN χ η).starProjection_apply_mem x.val).1.1⟩
  have hy : y ∈ cuspidalNewSignParitySpace N hN χ η :=
    (completedNewSignParitySpace N hN χ η).starProjection_apply_mem x.val
  have heq : (cuspidalNewSignParitySpace N hN χ η).starProjection x = y := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hy
    intro z hz
    exact (completedNewSignParitySpace N hN χ η).starProjection_inner_eq_zero x.val z.val hz
  exact congrArg Subtype.val heq

theorem cuspidalNewSignParityProjection_band {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (χ : admissibleGeneratorIndex N hN → ℂ)
    (η a b : ℝ) (x : localCuspidalSpace N hN) (hx : x ∈ S.band a b) :
    (cuspidalNewSignParitySpace N hN χ η).starProjection x ∈ S.band a b := by
  let U := (completedNewSignParitySpace N hN χ η).starProjection
  have hc (y : AutomorphicSpace N) (_hy : y ∈ localCuspidalSpace N hN) :
      U y ∈ localCuspidalSpace N hN :=
    ((completedNewSignParitySpace N hN χ η).starProjection_apply_mem y).1.1
  have hh := wave_commuting_cusp_band S U hc (completedNewSignParityProjection_wave N hN χ η)
    a b x hx
  have heq : U.toLinearMap.restrict hc x =
      (cuspidalNewSignParitySpace N hN χ η).starProjection x :=
    Subtype.ext (cuspidalNewSignParityProjection_coe N hN χ η x).symm
  rwa [heq] at hh

/-- Exact commutation of the actual parity/sign and finite spectral projections. -/
theorem cuspidalNewSignParityProjection_band_commute {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (χ : admissibleGeneratorIndex N hN → ℂ) (η a b : ℝ) :
    Commute (S.band a b).starProjection (cuspidalNewSignParitySpace N hN χ η).starProjection :=
  invariantSpace_projection_commute (S.band a b) (cuspidalNewSignParitySpace N hN χ η).starProjection
    (isSelfAdjoint_starProjection _) (cuspidalNewSignParityProjection_band S χ η a b)

/-- The existing finite physical sector is the restriction of the original
completed new/sign/parity source, including the parity condition. -/
theorem sectorParityBandSpace_mem_completedParity {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (hAd : GridAdmissibleGap.Admissible N)
    (a b η : ℝ) (hη : η ^ 2 = 1) (e : Sector N) (x : S.parityBand a b η) :
    x ∈ sectorParityBandSpace S a b η e ↔
      inclusion S a b η x ∈ completedNewSignParitySpace N hN (sectorCharacter N hN e) η := by
  rw [sectorParityBandSpace_eq_canonical S a b η e hAd]
  change inclusion S a b η x ∈ completedNewSignSpace N hN (sectorCharacter N hN e) ↔
    inclusion S a b η x ∈ completedNewSignSpace N hN (sectorCharacter N hN e) ∧
      inclusion S a b η x ∈ completedParitySpace N η
  have hp : inclusion S a b η x ∈ completedParitySpace N η :=
    (mem_completedParitySpace N η _).mpr
      ((mem_bandParity_iff_fixed S a b η hη x.val).mp x.property)
  exact ⟨fun hx => ⟨hx, hp⟩, fun hx => hx.1⟩

/-- The finite canonical sector projection is literally the restriction of
the actual completed new/sign/parity orthogonal projection. -/
theorem sectorParityBandProjection_coe {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (hAd : GridAdmissibleGap.Admissible N)
    (a b η : ℝ) (hη : η ^ 2 = 1) (e : Sector N) (x : S.parityBand a b η) :
    inclusion S a b η ((sectorParityBandSpace S a b η e).starProjection x) =
      (completedNewSignParitySpace N hN (sectorCharacter N hN e) η).starProjection
        (inclusion S a b η x) := by
  let χ := sectorCharacter N hN e
  let K := cuspidalNewSignParitySpace N hN χ η
  let Q := K.starProjection
  have hySpace : (Q x.val.val : AutomorphicSpace N) ∈ completedNewSignParitySpace N hN χ η :=
    K.starProjection_apply_mem x.val.val
  have hyBand : Q x.val.val ∈ S.band a b :=
    cuspidalNewSignParityProjection_band S χ η a b x.val.val x.val.property
  let yBand : S.band a b := ⟨Q x.val.val, hyBand⟩
  have hyParity : yBand ∈ S.parityBand a b η :=
    (mem_bandParity_iff_fixed S a b η hη yBand).mpr
      ((mem_completedParitySpace N η _).mp hySpace.2)
  let y : S.parityBand a b η := ⟨yBand, hyParity⟩
  have hy : y ∈ sectorParityBandSpace S a b η e :=
    (sectorParityBandSpace_mem_completedParity S hAd a b η hη e y).mpr hySpace
  have heq : (sectorParityBandSpace S a b η e).starProjection x = y := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hy
    intro z hz
    have hzK : z.val.val ∈ K :=
      (sectorParityBandSpace_mem_completedParity S hAd a b η hη e z).mp hz
    exact K.starProjection_inner_eq_zero x.val.val z.val.val hzK
  exact (congrArg (inclusion S a b η) heq).trans
    (cuspidalNewSignParityProjection_coe N hN χ η x.val.val)

#print axioms cuspidalNewSignParitySpace_closed
#print axioms completedNewSignParityProjection_wave
#print axioms cuspidalNewSignParityProjection_coe
#print axioms cuspidalNewSignParityProjection_band
#print axioms cuspidalNewSignParityProjection_band_commute
#print axioms sectorParityBandSpace_mem_completedParity
#print axioms sectorParityBandProjection_coe

end QuantitativeNinaMaass
