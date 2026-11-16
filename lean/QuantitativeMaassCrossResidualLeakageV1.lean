module

public import QuantitativeMaassCrossGraphFluxV1
public import QuantitativeMaassCrossFluxVectorsV1
public import QuantitativeMaassEigenEnergyLiftV1
public import QuantitativeMaassSeparatedFluxV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane ContinuousLinearMap
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open QuantitativeArithmeticMaassWave
open scoped Topology ContDiff InnerProductSpace

namespace QuantitativeMaass

/-- A finite family of separated destination eigenvectors captures only
the two Bessel-controlled flux vectors. The source is any actual graph
vector with the stated residual, including a continuous-spectrum cylinder
column; no source eigenfamily or spectral discreteness is required. -/
theorem crossQuotientLocalization_residual_separated_mass {ι : Type*} [Fintype ι]
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
        (‖crossFluxEnergyOperator N M K hK mN hmN b C hgrad g‖^2 +
          ‖crossFluxAmbientOperator N M K hK mM hmM b C hgrad
              (graphEnergyLift M g ((μ : ℂ) • g + d)) -
            crossQuotientLocalization N M K hK b hbound d‖^2 / (1+μ)) := by
  classical
  let T := crossQuotientLocalization N M K hK b hbound
  let A := crossFluxEnergyOperator N M K hK mN hmN b C hgrad g
  let D := crossFluxAmbientOperator N M K hK mM hmM b C hgrad
    (graphEnergyLift M g ((μ : ℂ) • g + d)) - T d
  let u := fun i => ((Real.sqrt (1+r i))⁻¹ : ℂ) • eigenEnergyLift N (r i) (f i)
  have hu : Orthonormal ℂ u := eigenEnergyLift_orthonormal N r f hf hr hgraph
  have hsμ : 0 < Real.sqrt (1+μ) := Real.sqrt_pos.2 (by linarith)
  have hraw (i : ι) :
      ((r i - μ : ℝ) : ℂ) * inner ℂ (f i) (T g) =
        inner ℂ (eigenEnergyLift N (r i) (f i)) A - inner ℂ (f i) D := by
    have hh := crossQuotientLocalization_eigen_residual_flux N M b K hK hbK
      mN mM hmN hmM B C hB hbound hgrad hreal (r i) μ (f i) g d (hgraph i) hg
    rw [crossLocalEnergyFlux_vectors, graphEnergyLift_value M hg,
      graphEnergyLift_value N (hgraph i)] at hh
    change ((r i - μ : ℝ) : ℂ) * inner ℂ (f i) (T g) =
      inner ℂ (eigenEnergyLift N (r i) (f i)) A -
        inner ℂ (f i) (crossFluxAmbientOperator N M K hK mM hmM b C hgrad
          (graphEnergyLift M g ((μ : ℂ) • g + d))) + inner ℂ (f i) (T d) at hh
    rw [hh]
    dsimp only [D]
    rw [inner_sub_right]
    ring
  have hflux (i : ι) :
      (((Real.sqrt (1+r i))^2 - (Real.sqrt (1+μ))^2 : ℝ) : ℂ) *
          inner ℂ (f i) (T g) =
        (Real.sqrt (1+r i) : ℂ) * inner ℂ (u i) A - inner ℂ (f i) D := by
    rw [Real.sq_sqrt (show 0 ≤ 1+r i by linarith [hr i]),
      Real.sq_sqrt (show 0 ≤ 1+μ by linarith)]
    have he : ((1+r i-(1+μ) : ℝ) : ℂ) = ((r i-μ : ℝ) : ℂ) := by
      congr 1
      ring
    rw [he, hraw]
    congr 1
    change inner ℂ (eigenEnergyLift N (r i) (f i)) A =
      (Real.sqrt (1+r i) : ℂ) * inner ℂ
        (((Real.sqrt (1+r i))⁻¹ : ℂ) • eigenEnergyLift N (r i) (f i)) A
    rw [_root_.inner_smul_left]
    have hs : Real.sqrt (1+r i) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (by linarith [hr i]))
    have hc : (starRingEnd ℂ) (((Real.sqrt (1+r i))⁻¹ : ℝ) : ℂ) =
        (((Real.sqrt (1+r i))⁻¹ : ℝ) : ℂ) := Complex.conj_ofReal _
    simp only [Complex.ofReal_inv] at hc
    rw [hc]
    field_simp [Complex.ofReal_ne_zero.mpr hs]
  have hh := separated_flux_bessel u f hu hf A D
    (fun i => Real.sqrt (1+r i)) (Real.sqrt (1+μ)) L
    (fun _ => Real.sqrt_nonneg _) hsμ hL hsep
    (fun i => inner ℂ (f i) (T g)) hflux
  rw [Real.sq_sqrt (show 0 ≤ 1+μ by linarith)] at hh
  exact hh

#print axioms crossQuotientLocalization_residual_separated_mass

end QuantitativeMaass
