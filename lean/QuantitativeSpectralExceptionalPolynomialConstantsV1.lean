module

public import QuantitativeSpectralExceptionalPolynomialCoverV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalGeometry

open UpperHalfPlane Set AsymptoticCompactBranch
open AsymptoticCongruenceLabels AsymptoticRationalFreeness
open AsymptoticRegularBranchFamily QuantitativeSpectralObservability
open scoped MatrixGroups

/-- Finite actual matrix families share one cutoff-independent constant. -/
theorem exists_family_cover_cap_inverse {ι : Type*} [Finite ι]
    (N : ℕ) (hN : 0<N) (g : ι → GL (Fin 2) ℝ) :
    ∃ K : ℝ, 1≤K ∧ ∀ (H ε : ℝ) (_hε : 0<ε) (t : ℕ) (i : ι) (z : ℍ),
      z∈wideCompactCover N H →
      (cap ε t (g i • z))⁻¹ ≤ (max 1 (ε*K*(H+3)^2))^t := by
  choose K hK hb using fun i => exists_cover_cap_inverse N hN (g i)
  obtain ⟨B,hB⟩ := (Set.finite_range K).bddAbove
  refine ⟨max 1 B,le_max_left _ _,?_⟩
  intro H ε hε t i z hz
  apply (hb i H ε hε t z hz).trans
  apply pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _))
  apply max_le_max_left
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left ((hB ⟨i,rfl⟩).trans (le_max_right _ _)) hε.le) (sq_nonneg _)

/-- The identity and every suffix followed by a rational branch form a
fixed finite matrix family. The bound includes all natural suffix indices. -/
theorem exists_word_cover_cap_inverse {ι κ : Type*} [Fintype ι] [Fintype κ]
    (N : ℕ) (hN : 0<N) (b : ι → Branch) (w : κ → ι → List SL(2,ℤ)) :
    ∃ K : ℝ, 1≤K ∧ ∀ (H ε : ℝ) (_hε : 0<ε) (t : ℕ) (z : ℍ),
      z∈wideCompactCover N H →
      (cap ε t z)⁻¹ ≤ (max 1 (ε*K*(H+3)^2))^t ∧
      ∀ j i k, (cap ε t
        ((realMatrix (rationalGL ((w j i).drop k).prod)*realMatrix (b i).matrix) • z))⁻¹ ≤
          (max 1 (ε*K*(H+3)^2))^t := by
  let J := Option (Σ j : κ, Σ i : ι, Fin ((w j i).length+1))
  let f : J → GL (Fin 2) ℝ
    | none => 1
    | some ⟨j,i,k⟩ => realMatrix (rationalGL ((w j i).drop k.val).prod)*realMatrix (b i).matrix
  obtain ⟨K,hK,hb⟩ := exists_family_cover_cap_inverse N hN f
  refine ⟨K,hK,?_⟩
  intro H ε hε t z hz
  refine ⟨by simpa only [f,one_smul] using hb H ε hε t none z hz,?_⟩
  intro j i k
  by_cases hk : k≤(w j i).length
  · exact hb H ε hε t (some ⟨j,i,⟨k,Nat.lt_succ_of_le hk⟩⟩) z hz
  · have hh := hb H ε hε t (some ⟨j,i,⟨(w j i).length,Nat.lt_succ_self _⟩⟩) z hz
    simpa only [f,List.drop_length,List.drop_eq_nil_of_le (le_of_not_ge hk),List.prod_nil] using hh

#print axioms exists_word_cover_cap_inverse

end QuantitativeSpectralExceptionalGeometry
