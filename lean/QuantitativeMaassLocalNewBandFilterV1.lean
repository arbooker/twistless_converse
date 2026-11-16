module

public import QuantitativeMaassWidePhysicalFilterEnergyV1
public import QuantitativeMaassOldFilterContractionV1
public import QuantitativeArithmeticRepeatedTwoBandsV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory Module QuantitativeNinaMaass
open scoped Topology
namespace QuantitativeMaass

local instance (N : ℕ) (hN : 0 < N) :
    NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance

local instance (N : ℕ) (hN : 0 < N) :
    InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance

local instance {N : ℕ} {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance

local instance {N : ℕ} {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance

local instance {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    NormedAddCommGroup (S.parityBand a b σ) := inferInstance

local instance {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    InnerProductSpace ℂ (S.parityBand a b σ) := inferInstance

local instance {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    FiniteDimensional ℂ (S.parityBand a b σ) := by
  let := S.band_finiteDimensional a b
  infer_instance



local instance {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    CompleteSpace (S.parityBand a b σ) := FiniteDimensional.complete ℂ _

local instance {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ)
    (U : Submodule ℂ (S.parityBand a b σ)) : U.HasOrthogonalProjection := by
  let : CompleteSpace U := FiniteDimensional.complete ℂ _
  infer_instance


/-- The simple-prime filter uses the genuine cover and trace operators. -/
def simpleNewBandFilter {M : ℕ} [NeZero M] {hM : 0<M}
    (S : CuspEnergySpectrum M hM) (p : ℕ) [Fact p.Prime]
    (T : CuspEnergySpectrum (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (a b σ : ℝ) (m : ℕ) : T.parityBand a b σ →L[ℂ] T.parityBand a b σ :=
  ((1-(1/2:ℂ) • oldBandSum S p T a b σ)^m).toContinuousLinearMap

theorem simpleNewBandFilter_norm {M : ℕ} [NeZero M] {hM : 0<M}
    (S : CuspEnergySpectrum M hM) (p : ℕ) [Fact p.Prime]
    (T : CuspEnergySpectrum (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (hpM : ¬p∣M) (a b σ : ℝ) (m : ℕ) :
    ‖simpleNewBandFilter S p T a b σ m‖≤1 := by
  have hcop := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpM
  have huv : (p:ℤ)*Nat.gcdA p M+(M:ℤ)*Nat.gcdB p M=1 := by
    rw [←Nat.gcd_eq_gcd_ab,hcop.gcd_eq_one,Int.natCast_one]
  obtain ⟨hA,hAA,hB,hBB⟩ := oldBand_projections S p T hpM
    (Nat.gcdA p M) (Nat.gcdB p M) huv a b σ
  exact two_projection_filter_norm _ _ hA hB hAA hBB m

/-- The error is measured against the actual trace-new projection. -/
theorem simpleNewBandFilter_weighted_energy {M : ℕ} [NeZero M] {hM : 0<M}
    (S : CuspEnergySpectrum M hM) (p : ℕ) [Fact p.Prime]
    (T : CuspEnergySpectrum (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (hpM : ¬p∣M) (σ D W : ℝ) (hD : 0≤D)
    (b : (t : ℝ) → OrthonormalBasis
      (Fin (finrank ℂ (T.parityBand (t-Real.exp (D*fourthRootScale t)) (t+Real.exp (D*fourthRootScale t)) σ))) ℂ
      (T.parityBand (t-Real.exp (D*fourthRootScale t)) (t+Real.exp (D*fourthRootScale t)) σ))
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => Real.exp (W*fourthRootScale t)*
      finiteBandEnergy (b t)
        (simpleNewBandFilter S p T (t-Real.exp (D*fourthRootScale t))
          (t+Real.exp (D*fourthRootScale t)) σ (growingMomentDegree t)-
          (S.traceNewParityBand T (Nat.dvd_mul_left M p)
            (t-Real.exp (D*fourthRootScale t)) (t+Real.exp (D*fourthRootScale t)) σ).starProjection)/(t*ε t))
      atTop (𝓝 0) := by
  have hcop := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpM
  have huv : (p:ℤ)*Nat.gcdA p M+(M:ℤ)*Nat.gcdB p M=1 := by
    rw [←Nat.gcd_eq_gcd_ab,hcop.gcd_eq_one,Int.natCast_one]
  have hk (a c : ℝ) := oldBandSum_kernel S p T hpM (Nat.gcdA p M) (Nat.gcdB p M) huv a c σ
  simpa only [simpleNewBandFilter,hk] using
    weighted_wide_physical_old_filter_energy S p T hpM σ D W hD b ε hε hproduct

/-- At a repeated prime two the finite polynomial is already exact. -/
theorem repeatedTwoNewBandFilter_eq (L : ℕ) (hL : 0<L)
    [NeZero (2*L)] [NeZero (2*(2*L))]
    (S : CuspEnergySpectrum (2*L) (QuantitativeArithmeticRepeatedTwoBands.twice_pos L hL))
    (T : CuspEnergySpectrum (2*(2*L)) (QuantitativeArithmeticRepeatedTwoBands.four_pos L hL))
    (a b σ : ℝ) :
    (LinearMap.toContinuousLinearMap (QuantitativeArithmeticRepeatedTwoBands.bandProjector L hL S T a b σ))=
      (S.traceNewParityBand T (Nat.dvd_mul_left (2*L) 2) a b σ).starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  exact QuantitativeArithmeticRepeatedTwoBands.bandProjector_eq L hL S T a b σ x

theorem repeatedTwoNewBandFilter_norm (L : ℕ) (hL : 0<L)
    [NeZero (2*L)] [NeZero (2*(2*L))]
    (S : CuspEnergySpectrum (2*L) (QuantitativeArithmeticRepeatedTwoBands.twice_pos L hL))
    (T : CuspEnergySpectrum (2*(2*L)) (QuantitativeArithmeticRepeatedTwoBands.four_pos L hL))
    (a b σ : ℝ) :
    ‖(LinearMap.toContinuousLinearMap (QuantitativeArithmeticRepeatedTwoBands.bandProjector L hL S T a b σ))‖≤1 := by
  rw [repeatedTwoNewBandFilter_eq]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using
    (S.traceNewParityBand T (Nat.dvd_mul_left (2*L) 2) a b σ).norm_starProjection_apply_le x

#print axioms simpleNewBandFilter_norm
#print axioms simpleNewBandFilter_weighted_energy
#print axioms repeatedTwoNewBandFilter_eq
#print axioms repeatedTwoNewBandFilter_norm
end QuantitativeMaass
