module

public import QuantitativeMaassNormalizerCuspidalV1
public import QuantitativeMaassCompletedLocalAtkinV1
public import QuantitativeMaassNewSignBandProjectionV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open QuantitativeNinaMaass QuantitativeNewGap
namespace QuantitativeMaass
local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    FiniteDimensional ℂ (S.band a b) := S.band_finiteDimensional a b

/-- The actual normalizer restricted to the closed cusp Hilbert space. -/
def cuspidalNormalizerPullback (N : ℕ) (hN : 0<N) (g : quotientNormalizerGroup N) :
    localCuspidalSpace N hN →ₗᵢ[ℂ] localCuspidalSpace N hN where
  toLinearMap := (quotientNormalizerPullback N g).toLinearMap.restrict
    (quotientNormalizerPullback_mem_cuspidal N hN g)
  norm_map' x := (quotientNormalizerPullback N g).norm_map x.val

/-- Actual rational normalizers preserve every principal spectral band. -/
theorem cuspidalNormalizerPullback_band {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)
    (g : quotientNormalizerGroup N) (a b : ℝ) (x : localCuspidalSpace N hN)
    (hx : x∈S.band a b) : cuspidalNormalizerPullback N hN g x∈S.band a b :=
  wave_commuting_cusp_band S (quotientNormalizerPullback N g).toContinuousLinearMap
    (quotientNormalizerPullback_mem_cuspidal N hN g) (quotientNormalizerPullback_wave N g) a b x hx

theorem cuspidalLocalAtkin_involutive (N : ℕ) (hN : 0<N) (p : SimplePrime N) :
    Function.Involutive (cuspidalNormalizerPullback N hN (completedLocalAtkinNormalizer N hN p)) := by
  intro x
  apply Subtype.ext
  exact completedLocalAtkin_involutive N hN p x.val

theorem cuspidalLocalAtkin_selfAdjoint (N : ℕ) (hN : 0<N) (p : SimplePrime N) :
    IsSelfAdjoint (cuspidalNormalizerPullback N hN (completedLocalAtkinNormalizer N hN p)).toContinuousLinearMap := by
  apply LinearMap.IsSymmetric.clm_adjoint_eq
  intro x y
  have hh := (cuspidalNormalizerPullback N hN (completedLocalAtkinNormalizer N hN p)).inner_map_map x
    (cuspidalNormalizerPullback N hN (completedLocalAtkinNormalizer N hN p) y)
  rw [cuspidalLocalAtkin_involutive N hN p y] at hh
  exact hh

/-- The canonical local Atkin involution commutes with the actual
orthogonal projection onto every finite spectral band. -/
theorem cuspidalLocalAtkin_band_commute {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)
    (p : SimplePrime N) (a b : ℝ) :
    Commute (S.band a b).starProjection
      (cuspidalNormalizerPullback N hN (completedLocalAtkinNormalizer N hN p)).toContinuousLinearMap :=
  invariantSpace_projection_commute (S.band a b) _ (cuspidalLocalAtkin_selfAdjoint N hN p)
    (cuspidalNormalizerPullback_band S (completedLocalAtkinNormalizer N hN p) a b)

#print axioms cuspidalNormalizerPullback_band
#print axioms cuspidalLocalAtkin_involutive
#print axioms cuspidalLocalAtkin_selfAdjoint
#print axioms cuspidalLocalAtkin_band_commute
end QuantitativeMaass
