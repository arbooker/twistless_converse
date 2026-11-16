module

public import QuantitativeMaassColumnLinearTraceV1
public import QuantitativeMaassAmbientParityFilterV1
public import QuantitativeMaassParityWindowDimensionV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open MeasureTheory ContinuousLinearMap QuantitativeNinaMaass AsymptoticSectorSigns
open AsymptoticClassicalPetersson QuantitativeArithmeticRepeatedTwoBands
namespace QuantitativeMaass
local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    FiniteDimensional ℂ (S.band a b) := S.band_finiteDimensional a b
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    NormedAddCommGroup (S.parityBand a b σ) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    InnerProductSpace ℂ (S.parityBand a b σ) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    FiniteDimensional ℂ (S.parityBand a b σ) := by
  let := S.band_finiteDimensional a b
  infer_instance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    CompleteSpace (S.parityBand a b σ) := FiniteDimensional.complete ℂ _

/-- The orthogonal projection in a finite spectral band is the actual
geometric parity projection under the original quotient inclusion. -/
theorem parityBand_projection_coe {N : ℕ} [NeZero N] {hN : 0<N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (hσ : σ^2=1) (x : S.band a b) :
    inclusion S a b σ ((S.parityBand a b σ).orthogonalProjectionOnto x)=
      parityProjection N σ (x.val:AutomorphicSpace N) := by
  let Q := S.bandParity a b σ
  have hs : Q.IsSymmetric := cuspWindowParity_symmetric N hN S.basis S.energy
    S.energy_nonneg S.graph a b σ
  have hi : IsIdempotentElem Q := cuspWindowParity_idempotent N hN S.basis S.energy
    S.energy_nonneg S.graph a b σ hσ
  have hx : (S.parityBand a b σ).starProjection x=Q x := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact ⟨x,rfl⟩
    · intro z hz
      obtain ⟨w,rfl⟩ := hz
      rw [inner_sub_left,hs x (Q w)]
      have hh : Q (Q w)=Q w := congrArg (fun A : S.band a b→ₗ[ℂ]S.band a b => A w) hi
      rw [hh,sub_self]
  change ((S.parityBand a b σ).starProjection x).val.val=_
  rw [hx]
  rfl

/-- Moving parity from observation to the finite-band input is exact for
the actual sector polynomial. -/
theorem columnLinearTrace_band_parity {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN)
    (a b σ : ℝ) (hσ : σ^2=1) (e : Sector N) (m : ℕ) (c : α→S.band a b) :
    columnLinearTrace μ (fun z => ambientSectorNewFilter N hN e m (c z).val.val)
      (parityProjection N σ)=
    columnLinearTrace μ (fun z => ambientSectorNewFilter N hN e m
      (inclusion S a b σ ((S.parityBand a b σ).orthogonalProjectionOnto (c z)))) 1 := by
  unfold columnLinearTrace
  apply integral_congr_ae
  filter_upwards with z
  let F := ambientSectorNewFilter N hN e m
  let v := F (c z).val.val
  have hh := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (parityProjection_selfAdjoint N σ) (parityProjection N σ v) v
  change inner ℂ (parityProjection N σ (parityProjection N σ v)) v=
    inner ℂ (parityProjection N σ v) (parityProjection N σ v) at hh
  rw [parityProjection_idempotent N σ hσ] at hh
  have hc : parityProjection N σ (F (c z).val.val)=F (parityProjection N σ (c z).val.val) :=
    DFunLike.congr_fun (ambientSectorNewFilter_parity N hN e m σ) (c z).val.val
  change (inner ℂ (parityProjection N σ v) v).re=_
  rw [hh]
  dsimp only [v]
  rw [hc,parityBand_projection_coe S a b σ hσ]
  rfl

#print axioms parityBand_projection_coe
#print axioms columnLinearTrace_band_parity
end QuantitativeMaass
