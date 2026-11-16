module

public import QuantitativeMaassEulerReconstructionV1
public import QuantitativeMaassEulerSectorsV1
public import AsymptoticReconstructedCountV1
public import QuantitativeHolomorphicGramV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane AsymptoticSectorSigns ContinuousLinearMap
open scoped Topology

namespace QuantitativeMaass
namespace EulerHilbert

variable {N Q : ℕ} {hQ : 0<Q} (A : FinitenessCertificate.Certificate N Q hQ)
  (hN : 0<N) (P : FinitenessGlobalHeight.Parameters A)

/-- One actual weight-zero extension per finite sector, with no spectral
parameter in its definition. -/
def reconstruction (e : Sector N) := AsymptoticCylinderReconstruction.extension A hN
  (AsymptoticReconstructedCount.parameters A P) (multiplier e) 0

theorem reconstruction_norm_le (e : Sector N) : ‖reconstruction A hN P e‖≤
    1+2*AsymptoticCertificateOperators.terminalConstant A (AsymptoticReconstructedCount.parameters A P) :=
  AsymptoticCylinderReconstruction.extension_norm_le A hN _ _ (fun q _ => multiplier_norm e q) 0
    (AsymptoticReconstructedCount.parameters_hyperbolic_contraction A hN P _ (fun q _ => multiplier_norm e q) 0)

theorem reconstruction_norm_ge (e : Sector N)
    (g : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε) :
    ‖g‖≤‖reconstruction A hN P e g‖ := by
  have hi := AsymptoticCylinderReconstruction.extension_inclusion_norm_ge A hN
    (AsymptoticReconstructedCount.parameters A P) (multiplier e) 0
    (lt_trans (AsymptoticReconstructedCount.parameters_hyperbolic_contraction A hN P _
      (fun q _ => multiplier_norm e q) 0) (by norm_num)) g
  apply hi.trans
  apply le_trans ((AsymptoticCylinder.inclusion (AsymptoticReconstructedCount.parameters A P).epsilon_pos).le_opNorm _)
  simpa only [one_mul,reconstruction] using! mul_le_mul_of_nonneg_right
    (AsymptoticCylinder.inclusion_norm_le _) (norm_nonneg _)

def normalized (e : Sector N) := QuantitativeHolomorphic.normalizedReconstruction (reconstruction A hN P e)

theorem normalized_norm (e : Sector N)
    (g : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε) :
    ‖normalized A hN P e g‖=‖g‖ := by
  apply QuantitativeHolomorphic.normalizedReconstruction_norm _ (by norm_num : (0:ℝ)<1)
  intro v
  simpa only [one_mul] using pow_le_pow_left₀ (norm_nonneg v) (reconstruction_norm_ge A hN P e v) 2

/-- Every original principal Euler solution lies in one of the finite exact
isometric reconstruction ranges, uniformly over the entire real parameter
line. Both the Hilbert realization and root sector are derived here. -/
theorem original_normalized_range (r : ℝ) (σ : ℕ) {b : ℕ → ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b) :
    ∃ (e : Sector N) (g : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε),
      (AsymptoticCylinderLift.lift (normalized A hN P e g) =ᵐ[volume]
        AsymptoticWeightedBranches.stripSection (AsymptoticReconstructedCount.parameters A P).ε
          ((AsymptoticReconstructedCount.parameters A P).s+3) 0 (principalEulerPhysical b r σ)) ∧
      ∀ q : ℕ,0<q → ∀ z : ℂ,0<z.im →
        FinitenessAnalyticReconstruction.twist (principalEulerPhysical b r σ) q z=
          multiplier e q*FinitenessAnalyticReconstruction.twist (principalEulerPhysical b r σ) q
            (-1/((Nat.lcm N (q^2):ℂ)*z)) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  obtain ⟨e,_,hFE⟩ := principalEulerPhysical_sector hN r σ hb
  obtain ⟨f,hf⟩ := principalEulerPhysical_exists_cylinder hN A P' r σ hb
  let g := AsymptoticRegionL2.restrict AsymptoticCylinder.measure
    (AsymptoticCylinderTerminal.region P'.ε) (AsymptoticCylinderTerminal.region_measurable P'.ε) f
  have he : reconstruction A hN P e g=f := by
    apply AsymptoticCylinderReconstruction.extension_of_FE A hN P' (multiplier e) 0
      (principalEulerPhysical b r σ) (principalEulerPhysical_periodic b r σ) _ f hf
      (lt_trans (AsymptoticReconstructedCount.parameters_hyperbolic_contraction A hN P _
        (fun q _ => multiplier_norm e q) 0) (by norm_num))
    intro q hq z hz
    simpa only [mul_zero,pow_zero,div_one] using hFE q (Nat.pos_of_dvd_of_pos hq hQ) z hz
  let R := reconstruction A hN P e
  refine ⟨e,(R.adjoint.comp R).comp (QuantitativeHolomorphic.inverseSqrtCFC (R.adjoint.comp R)) g,?_,hFE⟩
  have hn := QuantitativeHolomorphic.normalizedReconstruction_reconstruct R (by norm_num : (0:ℝ)<1)
    (fun v => by simpa only [one_mul] using pow_le_pow_left₀ (norm_nonneg v) (reconstruction_norm_ge A hN P e v) 2) g
  change AsymptoticCylinderLift.lift (QuantitativeHolomorphic.normalizedReconstruction R _) =ᵐ[volume] _
  rw [hn]
  exact he ▸ hf

#print axioms reconstruction_norm_le
#print axioms reconstruction_norm_ge
#print axioms normalized_norm
#print axioms original_normalized_range

end EulerHilbert
end QuantitativeMaass
