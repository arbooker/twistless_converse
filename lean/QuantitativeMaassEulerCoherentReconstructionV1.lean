module

public import QuantitativeMaassFullResidualFilterV1
public import QuantitativeMaassEulerRamifiedAverageV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass.EulerHilbert
open Set Filter MeasureTheory UpperHalfPlane AsymptoticSectorSigns ContinuousLinearMap
variable {N Q : ℕ} {hQ : 0<Q} (A : FinitenessCertificate.Certificate N Q hQ)
  (hN : 0<N) (P : FinitenessGlobalHeight.Parameters A)

/-- Every original principal Euler solution lies in one of the finite exact
isometric reconstruction ranges, uniformly over the entire real parameter
line. Both the Hilbert realization and root sector are derived here. -/
theorem original_normalized_coherent_range (r : ℝ) (σ : ℕ) {b : ℕ → ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b) :
    ∃ (e : Sector N) (g : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε),
      (AsymptoticCylinderLift.lift (normalized A hN P e g) =ᵐ[volume]
        AsymptoticWeightedBranches.stripSection (AsymptoticReconstructedCount.parameters A P).ε
          ((AsymptoticReconstructedCount.parameters A P).s+3) 0 (principalEulerPhysical b r σ)) ∧
      (∀ p,p∈simplePrimes N → delta e p=b p*(Real.sqrt p:ℂ)) ∧
      ∀ q : ℕ,0<q → ∀ z : ℂ,0<z.im →
        FinitenessAnalyticReconstruction.twist (principalEulerPhysical b r σ) q z=
          multiplier e q*FinitenessAnalyticReconstruction.twist (principalEulerPhysical b r σ) q
            (-1/((Nat.lcm N (q^2):ℂ)*z)) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  obtain ⟨e,hd,hFE⟩ := principalEulerPhysical_sector hN r σ hb
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
  refine ⟨e,(R.adjoint.comp R).comp (QuantitativeHolomorphic.inverseSqrtCFC (R.adjoint.comp R)) g,?_,hd,hFE⟩
  have hn := QuantitativeHolomorphic.normalizedReconstruction_reconstruct R (by norm_num : (0:ℝ)<1)
    (fun v => by simpa only [one_mul] using pow_le_pow_left₀ (norm_nonneg v) (reconstruction_norm_ge A hN P e v) 2) g
  change AsymptoticCylinderLift.lift (QuantitativeHolomorphic.normalizedReconstruction R _) =ᵐ[volume] _
  rw [hn]
  exact he ▸ hf

/-- The original weighted physical vector has coherent terminal data for
both the twist and ramified equations. -/
theorem original_coherent_physical_range (r : ℝ) (σ : ℕ) {b : ℕ→ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b) :
    ∃ (e : Sector N) (g : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε),
      FullTerminal.physicalIsometry A hN P e g=
        principalEulerWeightedLp hN A (AsymptoticReconstructedCount.parameters A P) r σ hb ∧
      (∀ p,p∈simplePrimes N → delta e p=b p*(Real.sqrt p:ℂ)) ∧
      ∀ q : ℕ,0<q → ∀ z : ℂ,0<z.im →
        FinitenessAnalyticReconstruction.twist (principalEulerPhysical b r σ) q z=
          multiplier e q*FinitenessAnalyticReconstruction.twist (principalEulerPhysical b r σ) q
            (-1/((Nat.lcm N (q^2):ℂ)*z)) := by
  obtain ⟨e,g,hg,hd,hFE⟩ := original_normalized_coherent_range A hN P r σ hb
  refine ⟨e,g,?_,hd,hFE⟩
  apply MeasureTheory.Lp.ext
  exact hg.trans (principalEulerWeightedLp_coeFn hN A
    (AsymptoticReconstructedCount.parameters A P) r σ hb).symm

#print axioms original_normalized_coherent_range
#print axioms original_coherent_physical_range
end QuantitativeMaass.EulerHilbert
