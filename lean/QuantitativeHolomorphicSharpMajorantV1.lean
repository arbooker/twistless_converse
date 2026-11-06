module

public import QuantitativeHolomorphicQuantifiedTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic.Sharp

open ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCylinder AsymptoticFourierNorm AsymptoticObservation

theorem inverseSqrtValue_growth {x : ℝ} (hx : 0≤x) (hx1 : x≤1) (n : ℕ) :
    inverseSqrtValue n x ≤ (3/2:ℝ)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hq := (inverseSqrt_invariant hx hx1 n).1
    have ht := mul_nonneg hx (sq_nonneg (inverseSqrtValue n x))
    have hu := mul_nonneg hq ht
    rw [inverseSqrtValue_succ]
    calc
      _ ≤ inverseSqrtValue n x*(3/2) := by nlinarith only [hu]
      _ ≤ (3/2:ℝ)^n*(3/2) := mul_le_mul_of_nonneg_right ih (by norm_num)
      _ = _ := (pow_succ _ _).symm

/-- Spectral majorant for the finite Newton normalizer, including singular
Grams. This controls the physical operator without coefficient-mass growth. -/
theorem inverseSqrtPolynomial_gram_norm_le {G H : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : G →L[ℂ] H) (hV : ‖V‖≤1) (n : ℕ) :
    ‖Polynomial.aeval (V.adjoint.comp V) (inverseSqrtPolynomial n)‖ ≤ (3/2:ℝ)^n := by
  have hA := (isPositive_adjoint_comp_self V).isSelfAdjoint
  have hspec : ∀ x ∈ spectrum ℝ (V.adjoint.comp V), 0≤x ∧ x≤1 :=
    reconstruction_gram_spectrum V (fun v => by simp) hV
  rw [←cfc_polynomial (inverseSqrtPolynomial n) (V.adjoint.comp V) hA]
  apply norm_cfc_le (by positivity)
  intro x hx
  have hp := hspec x hx
  rw [Real.norm_eq_abs]
  change |inverseSqrtValue n x|≤_
  rw [abs_of_nonneg (inverseSqrt_invariant hp.1 hp.2 n).1]
  exact inverseSqrtValue_growth hp.1 hp.2 n

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

theorem finiteCountWeightedNormalizer_norm_le (hN : 0<N) (P : Parameters A)
    (h : ℕ) (e : Sector N) (Y : ℝ) (j J n : ℕ) :
    ‖finiteCountWeightedNormalizer A hN P h e Y j J n‖ ≤ (3/2:ℝ)^n := by
  have hbase := scaled_norm_le_one (AsymptoticReconstructedCount.finiteCutBaseReconstruction
    A hN P h e Y j (Finset.Icc (-(J : ℤ)) J))
    (zero_lt_one.trans_le (countReconstructionBound_one_le A P))
    (AsymptoticReconstructedCount.finiteCutBaseReconstruction_norm_le A hN P h e Y j _)
  have hq := inverseSqrtPolynomial_gram_norm_le _
    (scaledCutFiniteCountReconstruction_norm_le A hN P h e Y j J) n
  exact (opNorm_comp_le _ _).trans ((mul_le_mul hbase hq (norm_nonneg _) zero_le_one).trans_eq (one_mul _))

theorem finiteCountReconstruction_fourier_gram (hN : 0 < N) (P : Parameters A)
    (h : ℕ) (e : Sector N) (Y : ℝ) (j J n l : ℕ) :
    ‖(polynomialNormalizedReconstruction (scaledCutFiniteCountReconstruction A hN P h e Y j J) n).adjoint
      ((fourierBasis (2*h) ((AsymptoticReconstructedCount.parameters A P).s+4)
        (by positivity : 0 < 4*Real.pi) (AsymptoticReconstructedCount.parameters A P).epsilon_pos l :
        holomorphicSpace (2*h) ((AsymptoticReconstructedCount.parameters A P).s+4)
          (by positivity : 0 < 4*Real.pi) (AsymptoticReconstructedCount.parameters A P).epsilon_pos) : Space)‖ ^ 2 ≤
      ((3/2:ℝ)^n)^2 *
        modeRatio (2*h) ((AsymptoticReconstructedCount.parameters A P).s+4) (4*Real.pi)
          (AsymptoticReconstructedCount.parameters A P).ε (l+1) := by
  rw [finiteCountReconstruction_weighted]
  apply (reconstructed_fourier_gram _ _ _ _ _ l).trans
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (finiteCountWeightedNormalizer_norm_le A hN P h e Y j J n) 2)
    (modeRatio_nonneg _ _ _ _ (AsymptoticReconstructedCount.parameters A P).epsilon_pos)

#print axioms inverseSqrtPolynomial_gram_norm_le
#print axioms finiteCountWeightedNormalizer_norm_le
#print axioms finiteCountReconstruction_fourier_gram

end QuantitativeHolomorphic.Sharp
