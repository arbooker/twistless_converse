module

public import QuantitativeArithmeticNewBandProductV1
public import QuantitativeMaassFiniteProductEnergyV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section

open QuantitativeNinaMaass QuantitativeArithmeticNewBandProjections
open QuantitativeArithmeticNewBandProduct
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

variable (N : ℕ) [NeZero N] (hN : 0<N)
    (T : CuspEnergySpectrum N hN)
    (S : ∀ p : ↥N.primeFactors, CuspEnergySpectrum (N/p.val)
      (prime_quotient_pos N p.val hN (Nat.prime_of_mem_primeFactors p.property)
        (Nat.dvd_of_mem_primeFactors p.property))) (a b σ : ℝ)


/-- A finite family of actual local approximants acts on the original
cusp parity band. The exact comparison is its total trace-new projection. -/
def totalNewBandApproximation
    (A : ↥N.primeFactors → T.parityBand a b σ →L[ℂ] T.parityBand a b σ) :
    T.parityBand a b σ →L[ℂ] T.parityBand a b σ :=
  ((Finset.univ : Finset ↥N.primeFactors).toList.map A).prod

theorem totalNewBandApproximation_norm
    (A : ↥N.primeFactors → T.parityBand a b σ →L[ℂ] T.parityBand a b σ)
    (hA : ∀ p,‖A p‖≤1) : ‖totalNewBandApproximation N hN T a b σ A‖≤1 :=
  contraction_list_prod _ A hA

/-- The local squared errors add with a constant depending only on the
number of prime divisors. The approximants need not commute. -/
theorem totalNewBandApproximation_energy {ι : Type*} [Fintype ι]
    (basis : OrthonormalBasis ι ℂ (T.parityBand a b σ))
    (A : ↥N.primeFactors → T.parityBand a b σ →L[ℂ] T.parityBand a b σ)
    (hA : ∀ p,‖A p‖≤1) :
    finiteBandEnergy basis
      (totalNewBandApproximation N hN T a b σ A-(totalNewBand N hN T a b σ).starProjection) ≤
      (4:ℝ)^((Finset.univ : Finset ↥N.primeFactors).toList.length)*
        ((Finset.univ : Finset ↥N.primeFactors).toList.map fun p =>
          finiteBandEnergy basis (A p-(localNewBand N hN T S a b σ p).starProjection)).sum := by
  rw [totalNewBand_projection N hN T S a b σ]
  apply finiteBandEnergy_product_difference basis _ A _ hA
  intro p
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using (localNewBand N hN T S a b σ p).norm_starProjection_apply_le x

#print axioms totalNewBandApproximation_norm
#print axioms totalNewBandApproximation_energy
end QuantitativeMaass
