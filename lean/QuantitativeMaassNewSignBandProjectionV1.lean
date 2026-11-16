module

public import QuantitativeMaassWaveBandInvariantV1
public import QuantitativeMaassNewSignWaveV1
public import QuantitativeMaassNormalizedNewSignEmbeddingV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set QuantitativeNinaMaass
open scoped InnerProductSpace

namespace QuantitativeMaass

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    FiniteDimensional ℂ (S.band a b) := S.band_finiteDimensional a b

/-- The projection formed inside cusp space is the restriction of the
original completed new/sign projection. -/
theorem cuspidalNewSignProjection_coe (N : ℕ) [NeZero N] (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN → ℂ) (x : localCuspidalSpace N hN) :
    ((cuspidalNewSignSpace N hN χ).starProjection x).val=
      (completedNewSignSpace N hN χ).starProjection x.val := by
  let y : localCuspidalSpace N hN :=
    ⟨(completedNewSignSpace N hN χ).starProjection x.val,
      ((completedNewSignSpace N hN χ).starProjection_apply_mem x.val).1⟩
  have hy : y∈cuspidalNewSignSpace N hN χ :=
    (completedNewSignSpace N hN χ).starProjection_apply_mem x.val
  have heq : (cuspidalNewSignSpace N hN χ).starProjection x=y := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hy
    intro z hz
    exact (completedNewSignSpace N hN χ).starProjection_inner_eq_zero x.val z.val hz
  exact congrArg Subtype.val heq

/-- The actual new/sign projection preserves every finite principal band. -/
theorem cuspidalNewSignProjection_band {N : ℕ} [NeZero N] {hN : 0<N}
    (S : CuspEnergySpectrum N hN) (χ : admissibleGeneratorIndex N hN → ℂ)
    (a b : ℝ) (x : localCuspidalSpace N hN) (hx : x∈S.band a b) :
    (cuspidalNewSignSpace N hN χ).starProjection x∈S.band a b := by
  let U := (completedNewSignSpace N hN χ).starProjection
  have hc (y : AutomorphicSpace N) (_hy : y∈localCuspidalSpace N hN) :
      U y∈localCuspidalSpace N hN := ((completedNewSignSpace N hN χ).starProjection_apply_mem y).1
  have hh := wave_commuting_cusp_band S U hc (completedNewSignProjection_wave N hN χ) a b x hx
  have heq : U.toLinearMap.restrict hc x=(cuspidalNewSignSpace N hN χ).starProjection x :=
    Subtype.ext (cuspidalNewSignProjection_coe N hN χ x).symm
  rwa [heq] at hh

/-- Exact commutation of the actual new/sign and spectral-band projections. -/
theorem cuspidalNewSignProjection_band_commute {N : ℕ} [NeZero N] {hN : 0<N}
    (S : CuspEnergySpectrum N hN) (χ : admissibleGeneratorIndex N hN → ℂ) (a b : ℝ) :
    Commute (S.band a b).starProjection (cuspidalNewSignSpace N hN χ).starProjection :=
  invariantSpace_projection_commute (S.band a b) (cuspidalNewSignSpace N hN χ).starProjection
    (isSelfAdjoint_starProjection _) (cuspidalNewSignProjection_band S χ a b)

#print axioms cuspidalNewSignProjection_coe
#print axioms cuspidalNewSignProjection_band
#print axioms cuspidalNewSignProjection_band_commute

end QuantitativeMaass
