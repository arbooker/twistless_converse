module

public import QuantitativeSpectralExceptionalPolynomialAssemblyV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalReducedRows

open UpperHalfPlane ContinuousLinearMap AsymptoticRegularBranchFamily AsymptoticCompactBranch
open AsymptoticCongruenceLabels AsymptoticRationalFreeness AsymptoticRationalBranches
open QuantitativeSpectralObservability QuantitativeSpectralExceptionalGeometry
open QuantitativeSpectralExceptionalUnweight (G Space)
open scoped MatrixGroups lp

/-- A genuine degree-at-most-4t polynomial bounds the actual selected
recombiner, with a cutoff-independent matrix constant and fixed word lengths. -/
theorem exists_selectedRecombine_polynomial_growth {ι κ : Type*} [Fintype ι] [Fintype κ]
    (N : ℕ) (hN : 0<N) (b : ι → Branch) (w : κ → ι → List SL(2,ℤ)) :
    ∃ K : ℝ, 1≤K ∧ ∀ (H ε : ℝ) (hε : 0<ε) (t : ℕ)
      (A : Finset SL(2,ℤ)) (hw : ∀ j i a, a∈w j i → a∈A)
      (c : ι → ℂ) (E : κ → Set ℍ)
      (Ds : QuantitativeSpectralExceptionalUnweight.Data (wideCompactCover N H) ε t)
      (Db : ∀ i, QuantitativeSpectralExceptionalUnweight.Data (image (b i) (wideCompactCover N H)) ε t)
      (x : ℍ),
      ‖selectedGeneratorRecombine A b w hw c E (wideCompactCover_compact N hN H) hε t Ds Db x‖ ≤
        (∑ j, (1+∑ i, ‖c i‖*((w j i).length:ℝ)))*(1+ε*K*(H+3)^2)^(2*t) := by
  obtain ⟨K,hK,hbound⟩ := exists_selectedRecombine_polynomial N hN b w
  refine ⟨K,hK,?_⟩
  intro H ε hε t A hw c E Ds Db x
  let P := (max 1 (ε*K*(H+3)^2))^t
  let Q := 1+ε*K*(H+3)^2
  have hP1 : 1≤P := one_le_pow₀ (le_max_left _ _)
  have hP0 : 0≤P := zero_le_one.trans hP1
  have hterm : 0≤ε*K*(H+3)^2 := by positivity
  have hQ1 : 1≤Q := by dsimp [Q]; linarith
  have hQ0 : 0≤Q := zero_le_one.trans hQ1
  have hPQ : P≤Q^t := by
    apply pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _))
    exact max_le hQ1 (by dsimp [Q]; linarith)
  have h2 : P*P≤Q^(2*t) := by
    apply (mul_le_mul hPQ hPQ hP0 (pow_nonneg hQ0 t)).trans_eq
    rw [←pow_add]
    congr 1
    omega
  have hP2 : P≤Q^(2*t) := (by nlinarith : P≤P*P).trans h2
  apply (hbound H ε hε t A hw c E Ds Db x).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  calc
    P+∑ i, ‖c i‖*P*((w j i).length*P) ≤
        Q^(2*t)+∑ i, (‖c i‖*((w j i).length:ℝ))*Q^(2*t) := by
      apply add_le_add hP2
      apply Finset.sum_le_sum
      intro i _
      calc
        _ = (‖c i‖*((w j i).length:ℝ))*(P*P) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (1+∑ i, ‖c i‖*((w j i).length:ℝ))*Q^(2*t) := by
      rw [add_mul,one_mul,Finset.sum_mul]

#print axioms exists_selectedRecombine_polynomial_growth

end QuantitativeSpectralExceptionalReducedRows
