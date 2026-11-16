module

public import QuantitativeMaassCrossResidualBoundV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane ContinuousLinearMap
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open QuantitativeArithmeticMaassWave
open scoped Topology ContDiff InnerProductSpace

namespace QuantitativeMaass

/-- Explicit separated-frequency leakage involving only the actual source
and its residual in L2, with all compact overlap and cutoff costs retained. -/
theorem crossQuotientLocalization_residual_L2_bound {ι : Type*} [Fintype ι]
    (N M : ℕ) (b : SmoothUpperSeed) (K : Set ℍ) (hK : IsCompact K)
    (hbK : tsupport (upperFunction b.toFun) ⊆ K) (mN mM : ℕ)
    (hmN : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ γ ∈ S, γ • z ∈ K) → S.card ≤ mN)
    (hmM : ∀ z : ℍ, ∀ S : Finset (gamma M),
      (∀ γ ∈ S, γ • z ∈ K) → S.card ≤ mM)
    (B C : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ z ∈ K, ‖upperFunction b.toFun z‖ ≤ B)
    (hgrad : ∀ z ∈ K, (upperEnergy b.toFun b.toFun z).re ≤ C^2)
    (hreal : ∀ Z, star (b.toFun Z) = b.toFun Z)
    (r : ι → ℝ) (μ : ℝ) (f : ι → AutomorphicSpace N)
    (g d : AutomorphicSpace M) (hf : Orthonormal ℂ f)
    (hr : ∀ i, 0 ≤ r i) (hμ : 0 ≤ μ)
    (hgraph : ∀ i, FriedrichsGraph N (f i) ((r i : ℂ) • f i))
    (hg : FriedrichsGraph M g ((μ : ℂ) • g + d))
    (L : ℝ) (hL : 0 < L)
    (hsep : ∀ i, L ≤ |Real.sqrt (1+r i) - Real.sqrt (1+μ)|) :
    ∑ i, ‖inner ℂ (f i) (crossQuotientLocalization N M K hK b hbound g)‖^2 ≤
      (2/L^2) *
        (5*(2*Real.sqrt (mN : ℝ) * |C| * Real.sqrt (mM : ℝ))^2*‖g‖^2 +
          (2*(2*Real.sqrt (mN : ℝ) * |C| * Real.sqrt (mM : ℝ))^2 +
            2*(Real.sqrt (mN : ℝ)*B*Real.sqrt (mM : ℝ))^2)*‖d‖^2/(1+μ)) := by
  have hleak := crossQuotientLocalization_residual_separated_mass N M b K hK hbK
    mN mM hmN hmM B C hB hbound hgrad hreal r μ f g d hf hr hμ hgraph hg L hL hsep
  apply hleak.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2/L^2)
  exact residual_flux_norm_bound
    (crossFluxEnergyOperator N M K hK mN hmN b C hgrad)
    (crossFluxAmbientOperator N M K hK mM hmM b C hgrad)
    (crossQuotientLocalization N M K hK b hbound) g d
    (graphEnergyLift M g ((μ : ℂ) • g + d))
    (2*Real.sqrt (mN : ℝ) * |C| * Real.sqrt (mM : ℝ))
    (Real.sqrt (mN : ℝ)*B*Real.sqrt (mM : ℝ)) μ (by positivity) (by positivity) hμ
    (crossFluxEnergyOperator_norm_le N M K hK mN mM hmN hmM b C hgrad)
    (crossFluxAmbientOperator_norm_le N M K hK mN mM hmN hmM b C hgrad)
    (crossQuotientLocalization_norm_le_of_overlap N M K hK b mN mM hmN hmM B hB hbound)
    (graphEnergyLift_residual_norm_sq_le M μ hμ g d hg)

#print axioms crossQuotientLocalization_residual_L2_bound

end QuantitativeMaass
