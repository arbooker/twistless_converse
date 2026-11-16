module

public import QuantitativeMaassTotalNewBandApproximationV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section

open Filter QuantitativeNinaMaass QuantitativeArithmeticNewBandProjections
open QuantitativeArithmeticNewBandProduct
open scoped Topology
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


/-- Local weighted squared errors imply the corresponding total-new
error on varying spectral bands. All subspaces are actual trace kernels. -/
theorem totalNewBandApproximation_weighted_limit
    (N : ℕ) [NeZero N] (hN : 0<N) (T : CuspEnergySpectrum N hN)
    (S : ∀ p : ↥N.primeFactors, CuspEnergySpectrum (N/p.val)
      (prime_quotient_pos N p.val hN (Nat.prime_of_mem_primeFactors p.property)
        (Nat.dvd_of_mem_primeFactors p.property)))
    (a b w : ℝ → ℝ) (σ : ℝ) (hw : ∀ᶠ t in atTop,0≤w t)
    (basis : (t : ℝ) → OrthonormalBasis
      (Fin (Module.finrank ℂ (T.parityBand (a t) (b t) σ))) ℂ (T.parityBand (a t) (b t) σ))
    (A : (t : ℝ) → ↥N.primeFactors → T.parityBand (a t) (b t) σ →L[ℂ] T.parityBand (a t) (b t) σ)
    (hA : ∀ t p,‖A t p‖≤1)
    (hlocal : ∀ p,Tendsto (fun t => w t*finiteBandEnergy (basis t)
      (A t p-(localNewBand N hN T S (a t) (b t) σ p).starProjection)) atTop (𝓝 0)) :
    Tendsto (fun t => w t*finiteBandEnergy (basis t)
      (totalNewBandApproximation N hN T (a t) (b t) σ (A t)-
        (totalNewBand N hN T (a t) (b t) σ).starProjection)) atTop (𝓝 0) := by
  classical
  let e (t : ℝ) (p : ↥N.primeFactors) := finiteBandEnergy (basis t)
    (A t p-(localNewBand N hN T S (a t) (b t) σ p).starProjection)
  have hsum (l : List ↥N.primeFactors) :
      Tendsto (fun t => (l.map fun p => w t*e t p).sum) atTop (𝓝 0) := by
    induction l with
    | nil => simp
    | cons p l ih =>
      simpa only [List.map_cons,List.sum_cons,add_zero] using (hlocal p).add ih
  let l := (Finset.univ : Finset ↥N.primeFactors).toList
  have hlim := (hsum l).const_mul ((4:ℝ)^l.length)
  simp only [mul_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hw] with t ht
    exact mul_nonneg ht (finiteBandEnergy_nonneg _ _)
  · filter_upwards [hw] with t ht
    have hbound := totalNewBandApproximation_energy N hN T S (a t) (b t) σ (basis t) (A t) (hA t)
    calc
      _ ≤ w t*((4:ℝ)^l.length*(l.map (e t)).sum) := mul_le_mul_of_nonneg_left hbound ht
      _ = (4:ℝ)^l.length*(l.map fun p => w t*e t p).sum := by
        rw [List.sum_map_mul_left]
        ring

#print axioms totalNewBandApproximation_weighted_limit
end QuantitativeMaass
