module

public import QuantitativeNinaMaassNewParityEnergyV1
public import QuantitativeMaassWaveBandInvariantV1
public import QuantitativeMaassPacketWaveCommuteV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter QuantitativeMaass AsymptoticClassicalPetersson
open scoped Topology InnerProductSpace SchwartzMap ContDiff

namespace QuantitativeNinaMaass

local instance (N : ℕ) (hN : 0 < N) : NormedAddCommGroup (localCuspidalSpace N hN) :=
  inferInstance
local instance (N : ℕ) (hN : 0 < N) : InnerProductSpace ℂ (localCuspidalSpace N hN) :=
  inferInstance
local instance {N : ℕ} {hN : 0 < N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0 < N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0 < N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    FiniteDimensional ℂ (S.band a b) := S.band_finiteDimensional a b

/-- Packet preservation of the actual completed new-parity space gives
commutation of its orthogonal projection with the genuine wave. -/
theorem completedNewParityProjection_wave (N : ℕ) [NeZero N] (hN : 0 < N)
    (η t : ℝ) :
    Commute (completedCuspidalNewParitySpace N hN η).starProjection
      (Wave.shiftedQuotientWave N t) := by
  apply timePacket_commuting_wave N _ _ t
  intro f hf he hc hr R hR hs
  apply invariantSpace_projection_commute
  · exact Wave.shiftedQuotientWavePacket_isSelfAdjoint N f _ hr
  · intro x hx
    refine ⟨⟨shiftedQuotientWavePacket_mem_localCuspidalSpace N hN f _ x hx.1.1,
      actualNewSpace_timePacket N hN f _ x hx.1.2⟩, ?_⟩
    exact completedParitySpace_timePacket N η (hc.toSchwartzMap hf) hc he hr R hR hs x hx.2

/-- The same physical projection, now restricted to the actual cusp
space; the restriction only packages the already proved inclusion. -/
def cuspNewParityProjection (N : ℕ) [NeZero N] (hN : 0 < N) (η : ℝ) :
    localCuspidalSpace N hN →ₗ[ℂ] localCuspidalSpace N hN :=
  (completedCuspidalNewParitySpace N hN η).starProjection.toLinearMap.restrict
    (fun x _ => ((completedCuspidalNewParitySpace N hN η).starProjection_apply_mem x).1.1)

theorem cuspNewParityProjection_band {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b η : ℝ)
    (x : localCuspidalSpace N hN) (hx : x ∈ S.band a b) :
    cuspNewParityProjection N hN η x ∈ S.band a b :=
  wave_commuting_cusp_band S _
    (fun y _ => ((completedCuspidalNewParitySpace N hN η).starProjection_apply_mem y).1.1)
    (completedNewParityProjection_wave N hN η) a b x hx

/-- Restriction of the genuine new-parity orthogonal projection to a
finite principal spectral band. -/
def bandNewParityProjection {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b η : ℝ) : S.band a b →ₗ[ℂ] S.band a b :=
  (cuspNewParityProjection N hN η).restrict
    (fun x hx => cuspNewParityProjection_band S a b η x hx)

theorem bandNewParityProjection_idempotent {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b η : ℝ) :
    IsIdempotentElem (bandNewParityProjection S a b η) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  exact DFunLike.congr_fun
    (completedCuspidalNewParitySpace N hN η).isIdempotentElem_starProjection
    (x.val : AutomorphicSpace N)

theorem bandNewParityProjection_symmetric {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b η : ℝ) :
    (bandNewParityProjection S a b η).IsSymmetric := by
  intro x y
  change inner ℂ ((completedCuspidalNewParitySpace N hN η).starProjection
      (x.val : AutomorphicSpace N)) (y.val : AutomorphicSpace N) =
    inner ℂ (x.val : AutomorphicSpace N)
      ((completedCuspidalNewParitySpace N hN η).starProjection (y.val : AutomorphicSpace N))
  exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (isSelfAdjoint_starProjection _) _ _

theorem mem_bandNewParityProjection_range {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b η : ℝ) (x : S.band a b) :
    x ∈ LinearMap.range (bandNewParityProjection S a b η) ↔
      (x.val : AutomorphicSpace N) ∈ completedCuspidalNewParitySpace N hN η := by
  constructor
  · rintro ⟨y, rfl⟩
    exact (completedCuspidalNewParitySpace N hN η).starProjection_apply_mem _
  · intro hx
    refine ⟨x, Subtype.ext (Subtype.ext ?_)⟩
    exact (completedCuspidalNewParitySpace N hN η).starProjection_eq_self_iff.mpr hx

theorem mem_bandParity_iff_fixed {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b η : ℝ) (hη : η ^ 2 = 1) (x : S.band a b) :
    x ∈ S.parityBand a b η ↔
      parityProjection N η (x.val : AutomorphicSpace N) = (x.val : AutomorphicSpace N) := by
  constructor
  · rintro ⟨y, rfl⟩
    exact parityProjection_idempotent N η hη (y.val : AutomorphicSpace N)
  · intro hx
    exact ⟨x, Subtype.ext (Subtype.ext hx)⟩

/-- The finite projection range is exactly the physical trace-new parity
band used by the checked all-admissible-level counting theorem. -/
def bandNewParityProjectionRangeEquiv {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b η : ℝ) (hη : η ^ 2 = 1) :
    LinearMap.range (bandNewParityProjection S a b η) ≃ₗ[ℂ]
      S.partialParityBand a b η univ where
  toFun x := by
    have hx := (mem_bandNewParityProjection_range S a b η x.val).mp x.property
    refine ⟨⟨x.val, (mem_bandParity_iff_fixed S a b η hη x.val).mpr
      ((mem_completedParitySpace N η _).mp hx.2)⟩, ?_⟩
    change (x.val.val : AutomorphicSpace N) ∈ partialNewSpace N hN univ
    rw [partialNewSpace_univ]
    exact hx.1.2
  invFun x := by
    refine ⟨x.val.val, (mem_bandNewParityProjection_range S a b η x.val.val).mpr ?_⟩
    refine ⟨⟨x.val.val.val.property, ?_⟩, ?_⟩
    · have hx := x.property
      change (x.val.val.val : AutomorphicSpace N) ∈ partialNewSpace N hN univ at hx
      rwa [partialNewSpace_univ] at hx
    · exact (mem_completedParitySpace N η _).mpr
        ((mem_bandParity_iff_fixed S a b η hη x.val.val).mp x.val.property)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- No simultaneous eigenbasis is needed: the sharp sum of the actual
new-parity projection weights equals the proved physical new dimension. -/
theorem sharp_newParity_weight_eq_dimension {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b η : ℝ) (hη : η ^ 2 = 1) :
    principalWindowWeight S.energy (newParitySpectralWeight S η) a b =
      (Module.finrank ℂ (S.partialParityBand a b η univ) : ℝ) := by
  have ho := S.basis.orthonormal.comp_linearIsometry (localCuspidalSpace N hN).subtypeₗᵢ
  let : Fintype (principalWindowIndices S.energy a b) :=
    (principalWindowIndices_finite N hN _ ho (fun j => (S.basis j).property)
      S.energy S.energy_nonneg S.graph a b).fintype
  have hh := finite_projection_energy_eq_finrank
    (cuspPrincipalWindowBasis N hN S.basis S.energy a b)
    (bandNewParityProjection S a b η)
    (bandNewParityProjection_idempotent S a b η)
    (bandNewParityProjection_symmetric S a b η)
  rw [(bandNewParityProjectionRangeEquiv S a b η hη).finrank_eq] at hh
  unfold principalWindowWeight
  rw [tsum_fintype, ← hh]
  apply Finset.sum_congr rfl
  intro i _
  change ‖(completedCuspidalNewParitySpace N hN η).starProjection
      (S.basis i.val : AutomorphicSpace N)‖ ^ 2 =
    ‖(completedCuspidalNewParitySpace N hN η).starProjection
      ((cuspPrincipalWindowBasis N hN S.basis S.energy a b i : localCuspidalSpace N hN) :
        AutomorphicSpace N)‖ ^ 2
  rw [cuspPrincipalWindowBasis_coe]

/-- The spectral projection weights in the packet identity inherit the
checked sharp newform Weyl law, with the original width hypotheses. -/
theorem newParitySpectralWeight_short_weyl (N : ℕ) [NeZero N]
    (hN : GridAdmissibleGap.Admissible N) (η : ℝ) (hη : η ^ 2 = 1) (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop, 0 < ε t ∧ ε t ≤ 1)
    (hproduct : Tendsto (fun t => ε t * slowScale t) atTop atTop) :
    Tendsto (fun t => principalWindowWeight (geometricCuspSpectrum N hN.1).energy
      (newParitySpectralWeight (geometricCuspSpectrum N hN.1) η) t (t + ε t) / (t * ε t))
      atTop (𝓝 (AsymptoticTotalNewCorner.arithmeticCoefficient N)) := by
  simpa only [sharp_newParity_weight_eq_dimension _ _ _ _ hη,
    partialParityCount_eq N hN.1] using actual_new_parity_short_weyl N hN η hη ε hε hproduct

#print axioms completedNewParityProjection_wave
#print axioms cuspNewParityProjection_band
#print axioms bandNewParityProjection_idempotent
#print axioms bandNewParityProjection_symmetric
#print axioms mem_bandNewParityProjection_range
#print axioms mem_bandParity_iff_fixed
#print axioms bandNewParityProjectionRangeEquiv
#print axioms sharp_newParity_weight_eq_dimension
#print axioms newParitySpectralWeight_short_weyl

end QuantitativeNinaMaass
