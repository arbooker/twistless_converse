module

public import QuantitativeMaassCrossEnergyFluxBoundV1
public import QuantitativeArithmeticMaassWaveEnergyRegularityV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane ContinuousLinearMap
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open QuantitativeArithmeticMaassWave
open scoped Topology ContDiff InnerProductSpace

namespace QuantitativeMaass

/-- The graph form identity in its conjugate-linear argument. -/
theorem cross_graphEnergyLift_form_left (N : ℕ) {f f₁ : AutomorphicSpace N}
    (hf : FriedrichsGraph N f f₁) (u : QuotientEnergySpace N) :
    quotientClosedEnergy N (graphEnergyLift N f f₁) u =
      inner ℂ f₁ (energyInclusion N u) := by
  have hh := congrArg (starRingEnd ℂ) (graphEnergyLift_form N hf u)
  have hc : (starRingEnd ℂ)
      (quotientClosedEnergy N u (graphEnergyLift N f f₁)) =
      quotientClosedEnergy N (graphEnergyLift N f f₁) u := by
    unfold quotientClosedEnergy
    rw [map_sub]
    exact congrArg₂ (· - ·)
      (_root_.inner_conj_symm (𝕜 := ℂ) (graphEnergyLift N f f₁) u)
      (_root_.inner_conj_symm (𝕜 := ℂ)
        (energyInclusion N (graphEnergyLift N f f₁)) (energyInclusion N u))
  rw [hc, _root_.inner_conj_symm (𝕜 := ℂ)] at hh
  exact hh

/-- Exact cross-quotient Green identity on the actual Friedrichs graphs.
The source quotient can be the cylinder; no point spectrum is assumed. -/
theorem crossQuotientLocalization_graph_flux (N M : ℕ)
    (b : SmoothUpperSeed) (K : Set ℍ) (hK : IsCompact K)
    (hbK : tsupport (upperFunction b.toFun) ⊆ K) (mN mM : ℕ)
    (hmN : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ γ ∈ S, γ • z ∈ K) → S.card ≤ mN)
    (hmM : ∀ z : ℍ, ∀ S : Finset (gamma M),
      (∀ γ ∈ S, γ • z ∈ K) → S.card ≤ mM)
    (B C : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ z ∈ K, ‖upperFunction b.toFun z‖ ≤ B)
    (hgrad : ∀ z ∈ K, (upperEnergy b.toFun b.toFun z).re ≤ C^2)
    (hr : ∀ Z, star (b.toFun Z) = b.toFun Z)
    {f f₁ : AutomorphicSpace N} {g g₁ : AutomorphicSpace M}
    (hf : FriedrichsGraph N f f₁) (hg : FriedrichsGraph M g g₁) :
    inner ℂ f₁ (crossQuotientLocalization N M K hK b hbound g) -
      inner ℂ f (crossQuotientLocalization N M K hK b hbound g₁) =
        crossLocalEnergyFlux N M K hK mN mM hmN hmM b C hgrad
          (graphEnergyLift N f f₁) (graphEnergyLift M g g₁) := by
  have hh := crossEnergyLocalization_flux N M b K hK hbK mN mM hmN hmM
    B C hB hbound hgrad hr (graphEnergyLift N f f₁) (graphEnergyLift M g g₁)
  rw [cross_graphEnergyLift_form_left N hf, graphEnergyLift_form M hg,
    crossEnergyLocalization_inclusion N M b K hK hbK mN mM hmN hmM
      B C hB hbound hgrad,
    crossEnergyLocalization_inclusion M N b K hK hbK mM mN hmM hmN
      B C hB hbound hgrad,
    graphEnergyLift_value M hg, graphEnergyLift_value N hf] at hh
  have hadj := crossQuotientLocalization_adjoint N M K hK b hbound
    (fun z _ => hr (z.re, z.im))
  rw [← hadj, ContinuousLinearMap.adjoint_inner_left] at hh
  exact hh

/-- The coefficient equation against a target eigenvector and a source
with an exact residual. Both spectral values are real, but the source
need not be an eigenvector. -/
theorem crossQuotientLocalization_eigen_residual_flux (N M : ℕ)
    (b : SmoothUpperSeed) (K : Set ℍ) (hK : IsCompact K)
    (hbK : tsupport (upperFunction b.toFun) ⊆ K) (mN mM : ℕ)
    (hmN : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ γ ∈ S, γ • z ∈ K) → S.card ≤ mN)
    (hmM : ∀ z : ℍ, ∀ S : Finset (gamma M),
      (∀ γ ∈ S, γ • z ∈ K) → S.card ≤ mM)
    (B C : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ z ∈ K, ‖upperFunction b.toFun z‖ ≤ B)
    (hgrad : ∀ z ∈ K, (upperEnergy b.toFun b.toFun z).re ≤ C^2)
    (hr : ∀ Z, star (b.toFun Z) = b.toFun Z)
    (r μ : ℝ) (f : AutomorphicSpace N) (g d : AutomorphicSpace M)
    (hf : FriedrichsGraph N f ((r : ℂ) • f))
    (hg : FriedrichsGraph M g ((μ : ℂ) • g + d)) :
    ((r - μ : ℝ) : ℂ) *
        inner ℂ f (crossQuotientLocalization N M K hK b hbound g) =
      crossLocalEnergyFlux N M K hK mN mM hmN hmM b C hgrad
        (graphEnergyLift N f ((r : ℂ) • f))
        (graphEnergyLift M g ((μ : ℂ) • g + d)) +
      inner ℂ f (crossQuotientLocalization N M K hK b hbound d) := by
  have hh := crossQuotientLocalization_graph_flux N M b K hK hbK mN mM hmN hmM
    B C hB hbound hgrad hr hf hg
  calc
    ((r - μ : ℝ) : ℂ) *
        inner ℂ f (crossQuotientLocalization N M K hK b hbound g) =
        (inner ℂ ((r : ℂ) • f)
            (crossQuotientLocalization N M K hK b hbound g) -
          inner ℂ f (crossQuotientLocalization N M K hK b hbound ((μ : ℂ) • g + d))) +
          inner ℂ f (crossQuotientLocalization N M K hK b hbound d) := by
      rw [map_add, map_smul, inner_add_right]
      have hl := _root_.inner_smul_left (𝕜 := ℂ) f
        (crossQuotientLocalization N M K hK b hbound g) (r : ℂ)
      have hright := _root_.inner_smul_right (𝕜 := ℂ) f
        (crossQuotientLocalization N M K hK b hbound g) (μ : ℂ)
      rw [hl, hright]
      simp only [Complex.conj_ofReal, Complex.ofReal_sub]
      ring
    _ = _ := by rw [hh]

#print axioms cross_graphEnergyLift_form_left
#print axioms crossQuotientLocalization_graph_flux
#print axioms crossQuotientLocalization_eigen_residual_flux

end QuantitativeMaass
