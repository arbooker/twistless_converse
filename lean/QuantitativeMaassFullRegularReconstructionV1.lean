module

public import QuantitativeMaassFullBranchExpressionV1
public import QuantitativeHolomorphicRegularNormalizationV1
public import QuantitativeMaassCoisometryNewtonV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open ContinuousLinearMap AsymptoticSectorSigns QuantitativeHolomorphic AsymptoticFiniteBranch
namespace QuantitativeMaass.EulerHilbert.FullTerminal

variable {N Q : ℕ} {hQ : 0<Q} (A : FinitenessCertificate.Certificate N Q hQ)
  (hN : 0<N) (P : FinitenessGlobalHeight.Parameters A)

/-- The regular counterpart of the raw Maass reconstruction, with the same
height exponent and without an additional capped-height multiplier. -/
def regularReconstruction (e : Sector N) (z : UpperHalfPlane) :=
  AsymptoticRegularReconstruction.extension A hN
    (AsymptoticReconstructedCount.parameters A P) (multiplier e) z

def finiteRegularReconstruction (e : Sector N) (z : UpperHalfPlane) (j J : ℕ) :=
  (AsymptoticRegularReconstruction.finiteFoldFull A hN
    (AsymptoticReconstructedCount.parameters A P) (multiplier e) j
    (Finset.Icc (-(J:ℤ)) J) z).comp
    (AsymptoticRegularReconstruction.TerminalSpace A (AsymptoticReconstructedCount.parameters A P) z).subtypeL

theorem regularReconstruction_bounds (e : Sector N) (z : UpperHalfPlane) :
    ‖regularReconstruction A hN P e z‖≤countReconstructionBound A P ∧
      ∀ x,‖x‖≤‖regularReconstruction A hN P e z x‖ := by
  have hc := AsymptoticRegularReconstruction.parameters_contraction A hN P
    (multiplier e) (fun q _ => multiplier_norm e q) z
  exact ⟨AsymptoticRegularReconstruction.extension_norm_le A hN _
    (multiplier e) (fun q _ => multiplier_norm e q) z hc,
    AsymptoticRegularReconstruction.extension_norm_ge A hN _
      (multiplier e) z (hc.trans (by norm_num))⟩

theorem finiteRegularReconstruction_norm (e : Sector N) (z : UpperHalfPlane) (j J : ℕ) :
    ‖finiteRegularReconstruction A hN P e z j J‖≤countReconstructionBound A P := by
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_left
    (AsymptoticRegularReconstruction.terminal_inclusion_norm_le A _ z) (norm_nonneg _)).trans
  rw [mul_one]
  exact AsymptoticRegularReconstruction.finiteFoldFull_norm_le A hN _
    (AsymptoticReconstructedCount.parameters_bound A P).le
    (multiplier e) (fun q _ => multiplier_norm e q) j (Finset.Icc (-(J:ℤ)) J) z

theorem finiteRegularReconstruction_error (e : Sector N) (z : UpperHalfPlane)
    (j J : ℕ) (hJ : 0<J) :
    ‖finiteRegularReconstruction A hN P e z j J-regularReconstruction A hN P e z‖≤
      countReconstructionError A P j J := by
  have he := regular_reconstruction_explicit_error A hN
    (AsymptoticReconstructedCount.parameters A P)
    (AsymptoticReconstructedCount.parameters_bound A P).le
    (multiplier e) (fun q _ => multiplier_norm e q) z j J hJ
  rw [finiteRegularReconstruction,regularReconstruction,←regular_full_subtype A hN _ e z,←sub_comp]
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_left
    (AsymptoticRegularReconstruction.terminal_inclusion_norm_le A _ z) (norm_nonneg _)).trans
  simpa only [mul_one,countReconstructionError] using he

def normalizedRegularReconstruction (e : Sector N) (z : UpperHalfPlane) :=
  normalizedReconstruction ((countReconstructionBound A P)⁻¹ • regularReconstruction A hN P e z)

def finiteNormalizedRegularReconstruction (e : Sector N) (z : UpperHalfPlane) (n j J : ℕ) :=
  polynomialNormalizedReconstruction
    ((countReconstructionBound A P)⁻¹ • finiteRegularReconstruction A hN P e z j J) n

theorem normalizedRegularReconstruction_norm (e : Sector N) (z : UpperHalfPlane) (x) :
    ‖normalizedRegularReconstruction A hN P e z x‖=‖x‖ := by
  have hh := scaled_reconstruction_bounds (regularReconstruction A hN P e z)
    (zero_lt_one.trans_le (countReconstructionBound_one_le A P))
    (regularReconstruction_bounds A hN P e z).1 (regularReconstruction_bounds A hN P e z).2
  exact normalizedReconstruction_norm _ (countGramLower_pos A P) hh.2 x

theorem finiteNormalizedRegularReconstruction_norm (e : Sector N) (z : UpperHalfPlane) (n j J : ℕ) :
    ‖finiteNormalizedRegularReconstruction A hN P e z n j J‖≤1 :=
  polynomialNormalizedReconstruction_norm_le _
    (scaled_norm_le_one _ (zero_lt_one.trans_le (countReconstructionBound_one_le A P))
      (finiteRegularReconstruction_norm A hN P e z j J)) n

/-- The identical explicit finite approximation error holds in the matching
regular representation. -/
theorem finiteNormalizedRegularReconstruction_error (e : Sector N) (z : UpperHalfPlane)
    (n j J : ℕ) (hJ : 0<J) :
    ‖finiteNormalizedRegularReconstruction A hN P e z n j J-normalizedRegularReconstruction A hN P e z‖≤
      countReconstructionError A P j J*(1+3*(3^n:ℕ))*(7:ℝ)^(4^n)+
        (1-countGramLower A P)^(2^n)/Real.sqrt (countGramLower A P) := by
  have hB : 0<countReconstructionBound A P := zero_lt_one.trans_le (countReconstructionBound_one_le A P)
  have hh := scaled_reconstruction_bounds (regularReconstruction A hN P e z) hB
    (regularReconstruction_bounds A hN P e z).1 (regularReconstruction_bounds A hN P e z).2
  exact finite_polynomial_normalization_closed_error _ _
    (countGramLower_pos A P) (countGramLower_le_one A P) hh.2 hh.1
    ((scaled_norm_le_one _ hB (finiteRegularReconstruction_norm A hN P e z j J)).trans (by norm_num))
    (scaled_difference_norm_le _ _ (inv_pos.mpr hB).le
      (inv_le_one_of_one_le₀ (countReconstructionBound_one_le A P))
      (finiteRegularReconstruction_error A hN P e z j J hJ)) n

#print axioms regularReconstruction_bounds
#print axioms finiteRegularReconstruction_norm
#print axioms finiteRegularReconstruction_error
#print axioms normalizedRegularReconstruction_norm
#print axioms finiteNormalizedRegularReconstruction_norm
#print axioms finiteNormalizedRegularReconstruction_error
end QuantitativeMaass.EulerHilbert.FullTerminal
