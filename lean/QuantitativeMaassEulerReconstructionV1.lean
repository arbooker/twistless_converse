module

public import QuantitativeMaassEulerWeightedL2V1
public import AsymptoticCylinderReconstructionV1
public import AsymptoticCylinderLiftRangeV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology

namespace QuantitativeMaass

/-- The original weighted wave has an actual cylinder representative; the
hyperbolic lift is exactly its capped physical strip section. -/
theorem principalEulerPhysical_exists_cylinder {N Q : ℕ} {hQ : 0<Q}
    (hN : 0<N) (A : FinitenessCertificate.Certificate N Q hQ)
    (P : FinitenessGlobalHeight.Parameters A) (r : ℝ) (σ : ℕ) {b : ℕ → ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b) :
    ∃ f : AsymptoticCylinder.Space,AsymptoticCylinderLift.lift f =ᵐ[volume]
      AsymptoticWeightedBranches.stripSection P.ε (P.s+3) 0 (principalEulerPhysical b r σ) := by
  let u := principalEulerWeightedLp hN A P r σ hb
  have hu := principalEulerWeightedLp_coeFn hN A P r σ hb
  have hs : ∀ᵐ z ∂volume,z∉AsymptoticMassTransport.strip → u z=0 := by
    filter_upwards [hu] with z hz hzs
    rw [hz]
    exact Set.indicator_of_notMem hzs _
  obtain ⟨f,hf⟩ := AsymptoticCylinderLift.exists_lift_of_support u hs
  exact ⟨f,hf ▸ hu⟩

/-- One certificate-dependent weight works for every principal parameter and
every original Euler solution. In each root sector the actual cylinder
extension is a bounded operator independent of the spectral parameter,
and it reconstructs the solution from its own terminal restriction. -/
theorem principalEulerPhysical_uniform_reconstruction {N Q : ℕ} {hQ : 0<Q}
    (hN : 0<N) (A : FinitenessCertificate.Certificate N Q hQ) :
    ∃ P : FinitenessGlobalHeight.Parameters A,
      (∀ χ : ℕ → ℂ,(∀ q,q∣Q → ‖χ q‖=1) →
        ‖AsymptoticCylinderReconstruction.extension A hN P χ 0‖≤
          1+2*AsymptoticCertificateOperators.terminalConstant A P) ∧
      ∀ (r : ℝ) (σ : ℕ) (b : ℕ → ℂ),MaassOriginal.IsEulerSolution N (.principal r) σ b →
        ∃ (χ : ℕ → ℂ) (f : AsymptoticCylinder.Space),(∀ q,‖χ q‖=1) ∧
          (AsymptoticCylinderLift.lift f =ᵐ[volume]
            AsymptoticWeightedBranches.stripSection P.ε (P.s+3) 0 (principalEulerPhysical b r σ)) ∧
          AsymptoticCylinderReconstruction.extension A hN P χ 0
            (AsymptoticRegionL2.restrict AsymptoticCylinder.measure
              (AsymptoticCylinderTerminal.region P.ε)
              (AsymptoticCylinderTerminal.region_measurable P.ε) f)=f := by
  obtain ⟨P₀⟩ := FinitenessGlobalHeight.parameters_exist hN hQ A
  obtain ⟨P,_,_,_,hK⟩ := AsymptoticCertificateOperators.contraction_parameters A hN P₀
  refine ⟨P,?_,?_⟩
  · intro χ hχ
    exact AsymptoticCylinderReconstruction.extension_norm_le A hN P χ hχ 0 (hK χ hχ 0)
  · intro r σ b hb
    obtain ⟨χ,hχ,hFE⟩ := principalEulerPhysical_original_FE hN r σ hb
    obtain ⟨f,hf⟩ := principalEulerPhysical_exists_cylinder hN A P r σ hb
    refine ⟨χ,f,hχ,hf,?_⟩
    apply AsymptoticCylinderReconstruction.extension_of_FE A hN P χ 0
      (principalEulerPhysical b r σ) (principalEulerPhysical_periodic b r σ) _ f hf
      (lt_trans (hK χ (fun q _ => hχ q) 0) (by norm_num))
    intro q hq z hz
    simpa only [mul_zero,pow_zero,div_one] using hFE q (Nat.pos_of_dvd_of_pos hq hQ) z hz

#print axioms principalEulerPhysical_exists_cylinder
#print axioms principalEulerPhysical_uniform_reconstruction

end QuantitativeMaass
