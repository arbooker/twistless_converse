module

public import QuantitativeHolomorphicNewtonTransportV1
public import QuantitativeHolomorphicRegularNormalizationV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open ContinuousLinearMap AsymptoticFiniteBranch

variable {N Q : ℕ} {hQ : 0 < Q} (A : Certificate N Q hQ)

/-- Compact regular approximation on terminal data. -/
def scaledCutFiniteRegularCountReconstruction (hN : 0 < N) (P : Parameters A)
    (e : Sector N) (z : UpperHalfPlane) (Y : ℝ) (d J : ℕ) :=
  let P' := AsymptoticReconstructedCount.parameters A P
  (countReconstructionBound A P)⁻¹ •
    ((AsymptoticRegularReconstruction.finiteCutFull A hN P' (multiplier e) Y d
      (Finset.Icc (-(J : ℤ)) J) z).comp
        (AsymptoticRegularReconstruction.TerminalSpace A P' z).subtypeL)

theorem cutFiniteRegularFull_error (hN : 0 < N) (P : Parameters A)
    (e : Sector N) (z : UpperHalfPlane) (Y : ℝ) (hY : 0 ≤ Y) (d J : ℕ) (hJ : 0 < J) :
    ‖AsymptoticRegularReconstruction.finiteCutFull A hN
        (AsymptoticReconstructedCount.parameters A P) (multiplier e) Y d
        (Finset.Icc (-(J : ℤ)) J) z -
      AsymptoticRegularReconstruction.includedFull A hN
        (AsymptoticReconstructedCount.parameters A P) (multiplier e) z‖ ≤
      cutCountReconstructionError A P Y d J := by
  have hraw := regular_reconstruction_explicit_error A hN
    (AsymptoticReconstructedCount.parameters A P)
    (AsymptoticReconstructedCount.parameters_bound A P).le
    (multiplier e) (fun q _ => multiplier_norm e q) z d J hJ
  have hf := (AsymptoticRegularReconstruction.finiteCutFull_error A hN
    (AsymptoticReconstructedCount.parameters A P) (multiplier e) Y d
      (Finset.Icc (-(J : ℤ)) J) z).trans hraw
  have hc := AsymptoticRegularReconstruction.cutFull_error A hN
    (AsymptoticReconstructedCount.parameters A P) (multiplier e)
    (fun q _ => multiplier_norm e q) Y hY z
    (AsymptoticRegularReconstruction.parameters_contraction A hN P (multiplier e)
      (fun q _ => multiplier_norm e q) z)
  apply (norm_sub_le_norm_sub_add_norm_sub _
    (AsymptoticRegularReconstruction.cutFull A hN
      (AsymptoticReconstructedCount.parameters A P) (multiplier e) Y z) _).trans
  apply add_le_add hf
  rw [norm_sub_rev]
  exact hc

theorem scaledCutFiniteRegularCountReconstruction_error (hN : 0 < N) (P : Parameters A)
    (e : Sector N) (z : UpperHalfPlane) (Y : ℝ) (hY : 0 ≤ Y) (d J : ℕ) (hJ : 0 < J) :
    ‖scaledCutFiniteRegularCountReconstruction A hN P e z Y d J -
      scaledRegularCountReconstruction A hN P e z‖ ≤ cutCountReconstructionError A P Y d J := by
  have hb := countReconstructionBound_one_le A P
  apply scaled_difference_norm_le _ _ (inv_nonneg.2 (zero_le_one.trans hb))
    (inv_le_one_of_one_le₀ hb)
  have he : AsymptoticRegularReconstruction.includedExtension A hN
      (AsymptoticReconstructedCount.parameters A P) (multiplier e) z =
      (AsymptoticRegularReconstruction.includedFull A hN
        (AsymptoticReconstructedCount.parameters A P) (multiplier e) z).comp
          (AsymptoticRegularReconstruction.TerminalSpace A
            (AsymptoticReconstructedCount.parameters A P) z).subtypeL := by
    rw [AsymptoticRegularReconstruction.includedExtension,
      AsymptoticRegularReconstruction.includedFull, comp_assoc, regular_full_subtype]
  rw [he, ← sub_comp]
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_left
    (AsymptoticRegularReconstruction.terminal_inclusion_norm_le A _ z) (norm_nonneg _)).trans
  simpa only [mul_one] using cutFiniteRegularFull_error A hN P e z Y hY d J hJ

theorem scaledCutFiniteRegularCountReconstruction_norm_le (hN : 0 < N) (P : Parameters A)
    (e : Sector N) (z : UpperHalfPlane) (Y : ℝ) (d J : ℕ) :
    ‖scaledCutFiniteRegularCountReconstruction A hN P e z Y d J‖ ≤ 1 := by
  apply scaled_norm_le_one _ (zero_lt_one.trans_le (countReconstructionBound_one_le A P))
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_left
    (AsymptoticRegularReconstruction.terminal_inclusion_norm_le A _ z) (norm_nonneg _)).trans
  rw [mul_one]
  exact AsymptoticRegularReconstruction.finiteCutFull_norm_le A hN _
    (AsymptoticReconstructedCount.parameters_bound A P).le (multiplier e)
    (fun q _ => multiplier_norm e q) Y d _ z

theorem cut_normalizedRegularCountReconstruction_closed_error (hN : 0 < N) (P : Parameters A)
    (e : Sector N) (z : UpperHalfPlane) (n : ℕ) (Y : ℝ) (hY : 0 ≤ Y)
    (d J : ℕ) (hJ : 0 < J) :
    ‖polynomialNormalizedReconstruction (scaledCutFiniteRegularCountReconstruction A hN P e z Y d J) n -
      normalizedReconstruction (scaledRegularCountReconstruction A hN P e z)‖ ≤
      cutCountReconstructionError A P Y d J * (1 + 3 * (3 ^ n : ℕ)) * (7 : ℝ) ^ (4 ^ n) +
        (1 - countGramLower A P) ^ (2 ^ n) / Real.sqrt (countGramLower A P) :=
  finite_polynomial_normalization_closed_error _ _ (countGramLower_pos A P)
    (countGramLower_le_one A P) (scaledRegularCountReconstruction_bounds A hN P e z).2
    (scaledRegularCountReconstruction_bounds A hN P e z).1
    ((scaledCutFiniteRegularCountReconstruction_norm_le A hN P e z Y d J).trans (by norm_num))
    (scaledCutFiniteRegularCountReconstruction_error A hN P e z Y hY d J hJ) n

theorem regularSum_scaledCutCountExpression (hN : 0 < N) (P : Parameters A)
    (e : Sector N) (z : UpperHalfPlane) (Y : ℝ) (d J : ℕ) :
    regularSum (scaledCutCountExpression A hN P e Y d J) z =
      (scaledCutFiniteRegularCountReconstruction A hN P e z Y d J).comp
        (AsymptoticRegularReconstruction.TerminalSpace A
          (AsymptoticReconstructedCount.parameters A P) z).subtypeL.adjoint := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let F := AsymptoticRegularReconstruction.finiteCutFull A hN P' (multiplier e) Y d
    (Finset.Icc (-(J : ℤ)) J) z
  let S := (AsymptoticRegularReconstruction.TerminalSpace A P' z).subtypeL
  let c := (countReconstructionBound A P)⁻¹
  have hright : F.comp (AsymptoticRegularCertificate.highProjection A P' z) = F :=
    AsymptoticRegularReconstruction.finiteCutFull_right_terminal A hN P'
      (multiplier e) Y d (Finset.Icc (-(J : ℤ)) J) z
  have hs : S.comp S.adjoint = AsymptoticRegularCertificate.highProjection A P' z :=
    AsymptoticOrbitRegion.subtype_comp_adjoint (G := AsymptoticRationalGroup.Group)
      (AsymptoticCertificateOperators.highStrip P'.ε) z
  have hf : (F.comp S).comp S.adjoint = F := by rw [comp_assoc, hs, hright]
  have hr : regularSum (scaledCutCountExpression A hN P e Y d J) z = (c : ℂ) • F :=
    (regularSum_scale (c : ℂ) _ z).trans
      (congrArg (fun T : AsymptoticRegularFoldedLow.Space →L[ℂ]
        AsymptoticRegularFoldedLow.Space => (c : ℂ) • T)
        (regularSum_cutFullExpression A hN P' (multiplier e) Y d
          (Finset.Icc (-(J : ℤ)) J) z))
  apply hr.trans
  apply (RCLike.real_smul_eq_coe_smul (K := ℂ) c F).symm.trans
  change c • F = (c • (F.comp S)).comp S.adjoint
  rw [smul_comp, hf]

theorem regularSum_normalizedCutCountExpression (hN : 0 < N) (P : Parameters A)
    (e : Sector N) (z : UpperHalfPlane) (n : ℕ) (Y : ℝ) (d J : ℕ) :
    regularSum (normalizedReconstructionExpression
      (scaledCutCountExpression A hN P e Y d J) n) z =
      (polynomialNormalizedReconstruction
        (scaledCutFiniteRegularCountReconstruction A hN P e z Y d J) n).comp
          (AsymptoticRegularReconstruction.TerminalSpace A
            (AsymptoticReconstructedCount.parameters A P) z).subtypeL.adjoint := by
  let S := (AsymptoticRegularReconstruction.TerminalSpace A
    (AsymptoticReconstructedCount.parameters A P) z).subtypeL
  have hS : S.adjoint.comp S = 1 :=
    AsymptoticOrbitRegion.adjoint_comp_subtype (G := AsymptoticRationalGroup.Group)
      (AsymptoticCertificateOperators.highStrip (AsymptoticReconstructedCount.parameters A P).ε) z
  have ht := polynomialNormalizedReconstruction_transport S hS
    (1 : AsymptoticRegularFoldedLow.Space →L[ℂ] AsymptoticRegularFoldedLow.Space)
    ((norm_map_iff_adjoint_comp_self
      (1 : AsymptoticRegularFoldedLow.Space →L[ℂ] AsymptoticRegularFoldedLow.Space)).1 (fun _ => rfl))
    (scaledCutFiniteRegularCountReconstruction A hN P e z Y d J) n
  have hh : polynomialNormalizedReconstruction
      ((scaledCutFiniteRegularCountReconstruction A hN P e z Y d J).comp S.adjoint) n =
      (polynomialNormalizedReconstruction (scaledCutFiniteRegularCountReconstruction A hN P e z Y d J) n).comp
        S.adjoint := by simpa only [one_def, id_comp] using ht
  exact (regularSum_normalizedReconstructionExpression _ n z).trans
    ((congrArg (fun T : AsymptoticRegularFoldedLow.Space →L[ℂ]
        AsymptoticRegularFoldedLow.Space => polynomialNormalizedReconstruction T n)
      (regularSum_scaledCutCountExpression A hN P e z Y d J)).trans hh)

/-- The identical common branch expression has the identical explicit
ambient approximation error in every regular orbit fiber. -/
theorem normalizedCutCountExpression_regular_ambient_error (hN : 0 < N) (P : Parameters A)
    (e : Sector N) (z : UpperHalfPlane) (n : ℕ) (Y : ℝ) (hY : 0 ≤ Y)
    (d J : ℕ) (hJ : 0 < J) :
    ‖regularSum (normalizedReconstructionExpression
        (scaledCutCountExpression A hN P e Y d J) n) z -
      (normalizedReconstruction (scaledRegularCountReconstruction A hN P e z)).comp
        (AsymptoticRegularReconstruction.TerminalSpace A
          (AsymptoticReconstructedCount.parameters A P) z).subtypeL.adjoint‖ ≤
      cutCountReconstructionError A P Y d J * (1 + 3 * (3 ^ n : ℕ)) * (7 : ℝ) ^ (4 ^ n) +
        (1 - countGramLower A P) ^ (2 ^ n) / Real.sqrt (countGramLower A P) := by
  let S := (AsymptoticRegularReconstruction.TerminalSpace A
    (AsymptoticReconstructedCount.parameters A P) z).subtypeL
  have hS : S.adjoint.comp S = 1 :=
    AsymptoticOrbitRegion.adjoint_comp_subtype (G := AsymptoticRationalGroup.Group)
      (AsymptoticCertificateOperators.highStrip (AsymptoticReconstructedCount.parameters A P).ε) z
  have he := norm_isometric_transport_difference_le S hS
    (1 : AsymptoticRegularFoldedLow.Space →L[ℂ] AsymptoticRegularFoldedLow.Space)
    ((norm_map_iff_adjoint_comp_self
      (1 : AsymptoticRegularFoldedLow.Space →L[ℂ] AsymptoticRegularFoldedLow.Space)).1 (fun _ => rfl))
    (polynomialNormalizedReconstruction (scaledCutFiniteRegularCountReconstruction A hN P e z Y d J) n)
    (normalizedReconstruction (scaledRegularCountReconstruction A hN P e z))
  have hh := he.trans (cut_normalizedRegularCountReconstruction_closed_error A hN P e z n Y hY d J hJ)
  simpa only [one_def, id_comp, regularSum_normalizedCutCountExpression] using hh

#print axioms normalizedCutCountExpression_regular_ambient_error

#print axioms cut_normalizedRegularCountReconstruction_closed_error
#print axioms regularSum_normalizedCutCountExpression

end QuantitativeHolomorphic
