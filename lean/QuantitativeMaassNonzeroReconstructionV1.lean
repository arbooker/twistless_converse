module

public import QuantitativeMaassNonzeroTerminalV1
public import QuantitativeMaassEulerNormalizationV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane AsymptoticSectorSigns ContinuousLinearMap
open scoped Topology

namespace QuantitativeMaass.EulerHilbert.Nonzero

variable {N Q : ℕ} {hQ : 0<Q} (A : FinitenessCertificate.Certificate N Q hQ)
  (hN : 0<N) (P : FinitenessGlobalHeight.Parameters A)


/-- Reconstruction restricted before normalization to terminal data with
vanishing horizontal constant mode. -/
def reconstruction (e : Sector N) := (EulerHilbert.reconstruction A hN P e).comp
    (terminalNonzeroInclusion (AsymptoticReconstructedCount.parameters A P).ε).toContinuousLinearMap

theorem reconstruction_norm_ge (e : Sector N)
    (g : terminalNonzeroModes (AsymptoticReconstructedCount.parameters A P).ε) :
    ‖g‖≤‖reconstruction A hN P e g‖ :=
  EulerHilbert.reconstruction_norm_ge A hN P e (terminalNonzeroInclusion _ g)

theorem reconstruction_norm_le (e : Sector N) : ‖reconstruction A hN P e‖≤
    1+2*AsymptoticCertificateOperators.terminalConstant A (AsymptoticReconstructedCount.parameters A P) := by
  apply le_trans (ContinuousLinearMap.opNorm_comp_le _ _)
  apply le_trans (mul_le_mul_of_nonneg_left
    (LinearIsometry.norm_toContinuousLinearMap_le _) (norm_nonneg (EulerHilbert.reconstruction A hN P e)))
  simpa only [mul_one] using EulerHilbert.reconstruction_norm_le A hN P e

def normalized (e : Sector N) :=
  QuantitativeHolomorphic.normalizedReconstruction
    (G := terminalNonzeroModes (AsymptoticReconstructedCount.parameters A P).ε)
    (H := AsymptoticCylinder.Space) (reconstruction A hN P e)

theorem normalized_norm (e : Sector N)
    (g : terminalNonzeroModes (AsymptoticReconstructedCount.parameters A P).ε) :
    ‖normalized A hN P e g‖=‖g‖ := by
  apply QuantitativeHolomorphic.normalizedReconstruction_norm _ (by norm_num : (0:ℝ)<1)
  intro v
  simpa only [one_mul] using pow_le_pow_left₀ (norm_nonneg v) (reconstruction_norm_ge A hN P e v) 2

/-- The physical reconstruction isometry uses the Gram normalization on
the nonzero-mode terminal space itself. -/
def physicalIsometry (e : Sector N) :
    terminalNonzeroModes (AsymptoticReconstructedCount.parameters A P).ε →ₗᵢ[ℂ]
      AsymptoticHyperbolicSlash.Space where
  toLinearMap := AsymptoticCylinderLift.lift.toLinearMap.comp (normalized A hN P e).toLinearMap
  norm_map' g := by
    change ‖AsymptoticCylinderLift.lift (normalized A hN P e g)‖=‖g‖
    rw [AsymptoticCylinderLift.lift_norm,normalized_norm]

/-- Every original principal Euler solution has exact normalized data in
the nonzero-mode terminal space, uniformly in its spectral parameter. -/
theorem original_normalized_range (r : ℝ) (σ : ℕ) {b : ℕ → ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b) :
    ∃ (e : Sector N) (g : terminalNonzeroModes (AsymptoticReconstructedCount.parameters A P).ε),
      physicalIsometry A hN P e g=
        principalEulerWeightedLp hN A (AsymptoticReconstructedCount.parameters A P) r σ hb ∧
      ∀ q : ℕ,0<q → ∀ z : ℂ,0<z.im →
        FinitenessAnalyticReconstruction.twist (principalEulerPhysical b r σ) q z=
          multiplier e q*FinitenessAnalyticReconstruction.twist (principalEulerPhysical b r σ) q
            (-1/((Nat.lcm N (q^2):ℂ)*z)) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  obtain ⟨e,_,hFE⟩ := principalEulerPhysical_sector hN r σ hb
  obtain ⟨f,hf⟩ := principalEulerPhysical_exists_cylinder hN A P' r σ hb
  have hfclass : AsymptoticCylinderLift.lift f=principalEulerWeightedLp hN A P' r σ hb := by
    apply Lp.ext
    exact hf.trans (principalEulerWeightedLp_coeFn hN A P' r σ hb).symm
  let g := AsymptoticRegionL2.restrict AsymptoticCylinder.measure
    (AsymptoticCylinderTerminal.region P'.ε) (AsymptoticCylinderTerminal.region_measurable P'.ε) f
  let g0 : terminalNonzeroModes P'.ε := ⟨g.val,original_terminal_nonzero hN A P' r σ hb f hfclass⟩
  have he : reconstruction A hN P e g0=f := by
    apply AsymptoticCylinderReconstruction.extension_of_FE A hN P' (multiplier e) 0
      (principalEulerPhysical b r σ) (principalEulerPhysical_periodic b r σ) _ f hf
      (lt_trans (AsymptoticReconstructedCount.parameters_hyperbolic_contraction A hN P _
        (fun q _ => multiplier_norm e q) 0) (by norm_num))
    intro q hq z hz
    simpa only [mul_zero,pow_zero,div_one] using hFE q (Nat.pos_of_dvd_of_pos hq hQ) z hz
  let R := reconstruction A hN P e
  have hn := QuantitativeHolomorphic.normalizedReconstruction_reconstruct R (by norm_num : (0:ℝ)<1)
    (fun v => by simpa only [one_mul] using pow_le_pow_left₀ (norm_nonneg v) (reconstruction_norm_ge A hN P e v) 2) g0
  refine ⟨e,(R.adjoint.comp R).comp
    (QuantitativeHolomorphic.inverseSqrtCFC
      (𝔄 := terminalNonzeroModes P'.ε →L[ℂ] terminalNonzeroModes P'.ε) (R.adjoint.comp R)) g0,?_,hFE⟩
  change AsymptoticCylinderLift.lift (QuantitativeHolomorphic.normalizedReconstruction R _)=_
  rw [hn,he,hfclass]

#print axioms reconstruction_norm_ge
#print axioms reconstruction_norm_le
#print axioms normalized_norm
#print axioms physicalIsometry
#print axioms original_normalized_range

end QuantitativeMaass.EulerHilbert.Nonzero
