module

public import QuantitativeMaassSectorParityNewtonLimitV1
public import QuantitativeMaassContractionTraceErrorV1

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory AsymptoticClassicalPetersson
open Filter QuantitativeNinaMaass QuantitativeNewGap AsymptoticSectorSigns
open QuantitativeArithmeticRepeatedTwoBands QuantitativeArithmeticNewBandProjections
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



local instance {N : ℕ} [NeZero N] {hN : 0<N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (K : Submodule ℂ (S.parityBand a b σ)) :
    CompleteSpace K := FiniteDimensional.complete ℂ _


/-- The finite compressed normalization has a dimension-free explicit norm bound. -/
theorem compressedNewtonPolynomial_norm {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (G P : E →L[ℂ] E) (hG : ‖G‖≤1) (hP : ‖P‖≤1) (n : ℕ) :
    ‖compressedNewtonPolynomial G P n‖≤(6:ℝ)^(4^n) := by
  have hp := (QuantitativeHolomorphic.polynomial_aeval_norm_le
    (QuantitativeHolomorphic.inverseSqrtPolynomial n) (extendedCompressedGram G P) (extendedCompressedGram_norm G P hG hP)).trans
      (by simpa only [show (3:ℝ)+3=6 by norm_num] using
        QuantitativeHolomorphic.polynomialMass_inverseSqrt_le (by norm_num : (0:ℝ)≤3) n)
  apply (norm_mul_le _ _).trans
  simpa only [one_mul] using mul_le_mul hP hp (norm_nonneg _) zero_le_one

/-- The quadratic trace bound also applies to explicitly bounded approximants. -/
theorem bounded_quadratic_trace_error {H ι : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype ι]
    (T : H →L[ℂ] H) (hT : ‖T‖≤1) (v w : ι → H) {K : ℝ}
    (hv : ∀ i,‖v i‖≤K) (hw : ∀ i,‖w i‖≤K) :
    (∑ i,((inner ℂ (T (w i)) (w i)).re-(inner ℂ (T (v i)) (v i)).re))^2≤
      16*K^2*(Fintype.card ι:ℝ)*(∑ i,‖w i-v i‖^2) := by
  classical
  let V := ∑ i,‖v i‖^2
  let E := ∑ i,‖w i-v i‖^2
  have hV : V≤K^2*(Fintype.card ι:ℝ) := by
    have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) =>
      pow_le_pow_left₀ (norm_nonneg _) (hv i) 2)
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm] using hh
  have hE : E≤4*K^2*(Fintype.card ι:ℝ) := by
    have hi (i : ι) : ‖w i-v i‖^2≤4*K^2 := by
      have hnorm := (norm_sub_le (w i) (v i)).trans (add_le_add (hw i) (hv i))
      have hs := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      nlinarith only [hs]
    have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hi i)
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm,mul_left_comm,mul_assoc] using hh
  have hV0 : 0≤V := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hE0 : 0≤E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hT2 : ‖T‖^2≤1 := by nlinarith [norm_nonneg T]
  have hfirst : 8*‖T‖^2*V*E≤8*K^2*(Fintype.card ι:ℝ)*E := by
    have hh := mul_le_mul hT2 hV hV0 (by norm_num : (0:ℝ)≤1)
    have hh' := mul_le_mul_of_nonneg_right hh hE0
    nlinarith only [hh']
  have hsecond : 2*‖T‖^2*E^2≤8*K^2*(Fintype.card ι:ℝ)*E := by
    have hh := mul_le_mul_of_nonneg_right hT2 (sq_nonneg E)
    have he := mul_le_mul_of_nonneg_right hE hE0
    nlinarith only [hh,he]
  have hh := finite_quadratic_trace_error T v w
  change _≤8*‖T‖^2*V*E+2*‖T‖^2*E^2 at hh
  change _≤16*K^2*(Fintype.card ι:ℝ)*E
  linarith

variable (N : ℕ) [NeZero N] (hN : 0<N) (T : CuspEnergySpectrum N hN)
    (a b σ : ℝ) {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)

/-- Actual weighted finite-band reconstruction from the specified sector operator. -/
def parityBandReconstruction (P : T.parityBand a b σ →L[ℂ] T.parityBand a b σ) (n : ℕ) :
    T.parityBand a b σ →L[ℂ] Lp ℂ 2 (quotientMeasure 0) :=
  (parityBandWeightedEmbedding N hN T a b σ hδ hν).comp
    (compressedNewtonPolynomial (parityBandWeightedGram N hN T a b σ hδ hν) P n)

theorem parityBandReconstruction_norm (P : T.parityBand a b σ →L[ℂ] T.parityBand a b σ)
    (hP : ‖P‖≤1) (n : ℕ) :
    ‖parityBandReconstruction N hN T a b σ hδ hν P n‖≤(6:ℝ)^(4^n) := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  simpa only [one_mul] using mul_le_mul
    (parityBandWeightedEmbedding_norm N hN T a b σ hδ hν)
    (compressedNewtonPolynomial_norm _ P (parityBandWeightedGram_norm N hN T a b σ hδ hν) hP n)
    (norm_nonneg _) zero_le_one

theorem parityBandReconstruction_trace_error {ι : Type*} [Fintype ι]
    (basis : OrthonormalBasis ι ℂ (T.parityBand a b σ))
    (P Q : T.parityBand a b σ →L[ℂ] T.parityBand a b σ) (hP : ‖P‖≤1) (hQ : ‖Q‖≤1)
    (A : Lp ℂ 2 (quotientMeasure 0) →L[ℂ] Lp ℂ 2 (quotientMeasure 0)) (hA : ‖A‖≤1) (n : ℕ) :
    (∑ i,((inner ℂ (A (parityBandReconstruction N hN T a b σ hδ hν Q n (basis i)))
        (parityBandReconstruction N hN T a b σ hδ hν Q n (basis i))).re-
      (inner ℂ (A (parityBandReconstruction N hN T a b σ hδ hν P n (basis i)))
        (parityBandReconstruction N hN T a b σ hδ hν P n (basis i))).re))^2≤
      16*((6:ℝ)^(4^n))^2*(Fintype.card ι:ℝ)*finiteSourceEnergy basis
        (parityBandReconstruction N hN T a b σ hδ hν Q n-
          parityBandReconstruction N hN T a b σ hδ hν P n) := by
  apply bounded_quadratic_trace_error A hA
  · intro i
    simpa only [basis.orthonormal.norm_eq_one i,mul_one] using
      (parityBandReconstruction N hN T a b σ hδ hν P n).le_of_opNorm_le
        (parityBandReconstruction_norm N hN T a b σ hδ hν P hP n) (basis i)
  · intro i
    simpa only [basis.orthonormal.norm_eq_one i,mul_one] using
      (parityBandReconstruction N hN T a b σ hδ hν Q n).le_of_opNorm_le
        (parityBandReconstruction_norm N hN T a b σ hδ hν Q hQ n) (basis i)

#print axioms compressedNewtonPolynomial_norm
#print axioms bounded_quadratic_trace_error
#print axioms parityBandReconstruction_norm
#print axioms parityBandReconstruction_trace_error
end QuantitativeMaass
