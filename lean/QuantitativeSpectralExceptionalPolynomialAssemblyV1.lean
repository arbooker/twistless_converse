module

public import QuantitativeSpectralExceptionalPolynomialConstantsV1
public import QuantitativeSpectralExceptionalPolynomialRecombineV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalReducedRows

open UpperHalfPlane ContinuousLinearMap AsymptoticRegularBranchFamily AsymptoticCompactBranch
open AsymptoticCongruenceLabels AsymptoticRationalFreeness AsymptoticRationalBranches
open QuantitativeSpectralObservability QuantitativeSpectralExceptionalGeometry
open QuantitativeSpectralExceptionalUnweight (G Space)
open scoped MatrixGroups lp

/-- The actual selected recombiner has a fixed polynomial cutoff bound.
It holds for the compactness-chosen Data already used in factorization;
only actual coefficients enter the estimate. -/
theorem exists_selectedRecombine_polynomial {ι κ : Type*} [Fintype ι] [Fintype κ]
    (N : ℕ) (hN : 0<N) (b : ι → Branch) (w : κ → ι → List SL(2,ℤ)) :
    ∃ K : ℝ, 1≤K ∧ ∀ (H ε : ℝ) (hε : 0<ε) (t : ℕ)
      (A : Finset SL(2,ℤ)) (hw : ∀ j i a, a∈w j i → a∈A)
      (c : ι → ℂ) (E : κ → Set ℍ)
      (Ds : QuantitativeSpectralExceptionalUnweight.Data (wideCompactCover N H) ε t)
      (Db : ∀ i, QuantitativeSpectralExceptionalUnweight.Data (image (b i) (wideCompactCover N H)) ε t)
      (x : ℍ),
      let P := (max 1 (ε*K*(H+3)^2))^t
      ‖selectedGeneratorRecombine A b w hw c E (wideCompactCover_compact N hN H) hε t Ds Db x‖ ≤
        ∑ j, (P+∑ i, ‖c i‖*P*((w j i).length*P)) := by
  obtain ⟨K,hK,hbound⟩ := exists_word_cover_cap_inverse N hN b w
  refine ⟨K,hK,?_⟩
  intro H ε hε t A hw c E Ds Db x
  let P := (max 1 (ε*K*(H+3)^2))^t
  have hP : 0≤P := by dsimp [P]; positivity
  have hbase : ∀ z∈wideCompactCover N H, (cap ε t z)⁻¹≤P :=
    fun z hz => (hbound H ε hε t z hz).1
  have hword : ∀ j i k z, z∈image (b i) (wideCompactCover N H) →
      (cap ε t (integralLabel ((w j i).drop k).prod • z))⁻¹≤P := by
    intro j i k z hz
    obtain ⟨y,hy,rfl⟩ := hz
    have hh := (hbound H ε hε t y hy).2 j i k
    rw [mul_smul] at hh
    have hb : realMatrix (b i).matrix • y = label (b i) • y :=
      (ofMatrix_action _ (b i).positive y).symm
    have hg : realMatrix (rationalGL ((w j i).drop k).prod) • (label (b i) • y) =
        integralLabel ((w j i).drop k).prod • (label (b i) • y) :=
      (ofMatrix_action _ (rationalGL_positive _) _).symm
    rwa [hb,hg] at hh
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_right (AsymptoticOrbitRegion.corner_norm_le _ _) (norm_nonneg _)).trans
  simp only [one_mul]
  apply generatorRecombine_norm_of_inverse A b (w j) (hw j) c
    (wideCompactCover_compact N hN H) hε t hP hbase ?_ (hword j) Ds Db x
  intro i z hz
  simpa only [List.drop_length,List.prod_nil,map_one,one_smul] using hword j i (w j i).length z hz

#print axioms exists_selectedRecombine_polynomial

end QuantitativeSpectralExceptionalReducedRows
