module

public import QuantitativeHolomorphicRegularSourceV1
public import AsymptoticIntegralCertificateV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared

open ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeHolomorphic AsymptoticSubgroupSupport AsymptoticIntegralSubgroup
open AsymptoticRegularReconstruction AsymptoticFiniteBranch Filter
open scoped Topology lp

/-- Newton normalization preserves each subgroup algebra at every finite stage. -/
theorem polynomial_normalization_supported {G : Type*} [Group G]
    (S : Subgroup G) (R : ℓ²(G, ℂ) →L[ℂ] ℓ²(G, ℂ)) (hR : Supported S R) (n : ℕ) :
    Supported S (polynomialNormalizedReconstruction R n) := by
  exact supported_comp S _ _ hR (supported_polynomial S _
    (supported_comp S _ _ (supported_adjoint S R hR) hR) (inverseSqrtPolynomial n))

variable {N Q : ℕ} {hQ : 0 < Q} (A : Certificate N Q hQ)

/-- Extending the scaled reconstruction by zero gives exactly the scaled
original ambient reconstruction. -/
theorem scaled_reconstruction_ambient_eq (hN : 0 < N) (P : Parameters A)
    (e : Sector N) (z : UpperHalfPlane) :
    (scaledRegularCountReconstruction A hN P e z).comp
      (TerminalSpace A (AsymptoticReconstructedCount.parameters A P) z).subtypeL.adjoint =
    (countReconstructionBound A P)⁻¹ • includedFull A hN
      (AsymptoticReconstructedCount.parameters A P) (multiplier e) z := by
  have he : includedExtension A hN (AsymptoticReconstructedCount.parameters A P)
      (multiplier e) z =
      (includedFull A hN (AsymptoticReconstructedCount.parameters A P) (multiplier e) z).comp
        (TerminalSpace A (AsymptoticReconstructedCount.parameters A P) z).subtypeL := by
    rw [includedExtension, includedFull, comp_assoc, regular_full_subtype]
  let P' := AsymptoticReconstructedCount.parameters A P
  have hs : (TerminalSpace A P' z).subtypeL.comp (TerminalSpace A P' z).subtypeL.adjoint =
      AsymptoticRegularCertificate.highProjection A P' z :=
    AsymptoticOrbitRegion.subtype_comp_adjoint _ z
  change ((countReconstructionBound A P)⁻¹ •
    includedExtension A hN P' (multiplier e) z).comp _ = _
  have hr := includedFull_right_terminal A hN P' (multiplier e) z
  have hh : (includedExtension A hN P' (multiplier e) z).comp
      (TerminalSpace A P' z).subtypeL.adjoint = includedFull A hN P' (multiplier e) z := by
    calc
      _ = ((includedFull A hN P' (multiplier e) z).comp
        (TerminalSpace A P' z).subtypeL).comp (TerminalSpace A P' z).subtypeL.adjoint :=
          congrArg (fun B => B.comp (TerminalSpace A P' z).subtypeL.adjoint) he
      _ = (includedFull A hN P' (multiplier e) z).comp
        ((TerminalSpace A P' z).subtypeL.comp (TerminalSpace A P' z).subtypeL.adjoint) :=
          comp_assoc _ _ _
      _ = _ := (congrArg (fun B => (includedFull A hN P' (multiplier e) z).comp B) hs).trans hr
  rw [smul_comp]
  exact congrArg (fun B => (countReconstructionBound A P)⁻¹ • B) hh

/-- The exact normalized reconstruction is supported at every prime avoiding
both the level and the fixed certificate modulus. No new denominators arise
from inverse-square-root normalization. -/
theorem normalized_reconstruction_supported (q : ℕ) [Fact q.Prime]
    (hN : 0 < N) (hqN : ¬q ∣ N) (hqQ : ¬q ∣ Q) (P : Parameters A)
    (e : Sector N) (z : UpperHalfPlane) :
    Supported (integralGroup q) (normalizedRegularAmbientCountReconstruction A hN P e z) := by
  let S := (TerminalSpace A (AsymptoticReconstructedCount.parameters A P) z).subtypeL
  let R := scaledRegularCountReconstruction A hN P e z
  have hS : S.adjoint.comp S = 1 :=
    AsymptoticOrbitRegion.adjoint_comp_subtype _ z
  have hR : Supported (integralGroup q) (R.comp S.adjoint) := by
    rw [show R.comp S.adjoint = _ from scaled_reconstruction_ambient_eq A hN P e z]
    have hf := includedFull_supported q A hN hqN hqQ _ _ z
      ((parameters_contraction A hN P (multiplier e) (fun r _ => multiplier_norm e r) z).trans
        (by norm_num))
    have he := RCLike.real_smul_eq_coe_smul (K := ℂ) (countReconstructionBound A P)⁻¹
      (includedFull A hN (AsymptoticReconstructedCount.parameters A P) (multiplier e) z)
    exact (congrArg (fun B => Supported (integralGroup q) B) he).mpr
      (supported_smul (integralGroup q) _ hf (((countReconstructionBound A P)⁻¹ : ℝ) : ℂ))
  have ht (n : ℕ) : polynomialNormalizedReconstruction (R.comp S.adjoint) n =
      (polynomialNormalizedReconstruction R n).comp S.adjoint := by
    simpa only [one_def, id_comp] using polynomialNormalizedReconstruction_transport S hS
      (1 : RegularSpace →L[ℂ] RegularSpace)
      ((norm_map_iff_adjoint_comp_self (1 : RegularSpace →L[ℂ] RegularSpace)).1 (fun _ => rfl)) R n
  apply supported_strong_limit (integralGroup q)
    (fun n => polynomialNormalizedReconstruction (R.comp S.adjoint) n) _
    (fun n => polynomial_normalization_supported _ _ hR n)
  have hn : Tendsto (fun n => polynomialNormalizedReconstruction R n) atTop
      (𝓝 (normalizedReconstruction R)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun n => norm_nonneg _)
      (fun n => normalizedRegularCountReconstruction_polynomial_error A hN P e z n)
      (normalized_newton_defect_tendsto A P)
  intro v
  simp only [ht, comp_apply]
  exact ((ContinuousLinearMap.apply ℂ AsymptoticRegularFoldedLow.Space
    (S.adjoint v)).continuous.tendsto _).comp hn

/-- Conjugating a source operator by the actual normalized reconstruction
preserves fresh-prime support. -/
theorem reconstructed_source_supported (q : ℕ) [Fact q.Prime]
    (hN : 0 < N) (hqN : ¬q ∣ N) (hqQ : ¬q ∣ Q) (P : Parameters A)
    (e : Sector N) (z : UpperHalfPlane) (F : RegularSpace →L[ℂ] RegularSpace)
    (hF : Supported (integralGroup q) F) :
    let U := normalizedRegularAmbientCountReconstruction A hN P e z
    Supported (integralGroup q) (U.comp (F.comp U.adjoint)) := by
  have hU := normalized_reconstruction_supported A q hN hqN hqQ P e z
  exact supported_comp _ _ _ hU
    (supported_comp _ _ _ hF (supported_adjoint _ _ hU))

#print axioms polynomial_normalization_supported
#print axioms scaled_reconstruction_ambient_eq
#print axioms normalized_reconstruction_supported
#print axioms reconstructed_source_supported

end QuantitativeEulerEndpointPrepared
