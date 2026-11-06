module

public import QuantitativeSpectralExceptionalPolynomialHeightV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalGeometry

open UpperHalfPlane Set AsymptoticCompactBranch
open AsymptoticCongruenceLabels AsymptoticCongruenceStrip QuantitativeSpectralObservability
open scoped MatrixGroups

/-- Every fixed real Möbius branch on the finite congruence cover has a
quadratic reciprocal-height polynomial, uniformly in the cusp cutoff. -/
theorem exists_cover_cap_inverse (N : ℕ) (hN : 0<N) (g : GL (Fin 2) ℝ) :
    ∃ K : ℝ, 1≤K ∧ ∀ (H ε : ℝ) (_hε : 0<ε) (t : ℕ) (z : ℍ),
      z∈wideCompactCover N H →
      (cap ε t (g • z))⁻¹ ≤ (max 1 (ε*K*(H+3)^2))^t := by
  let : NeZero N := ⟨hN.ne'⟩
  let f := fun q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N =>
    heightConstant (g * Matrix.SpecialLinearGroup.mapGL ℝ q.out⁻¹)
  obtain ⟨K,hK⟩ := (Set.finite_range f).bddAbove
  refine ⟨max 1 K,le_max_left _ _,?_⟩
  intro H ε hε t z hz
  obtain ⟨q,w,hw,rfl⟩ := mem_iUnion.mp hz
  dsimp only at *
  rw [←map_inv,integralLabel_action]
  have hh := wideBox_cap_inverse (g * Matrix.SpecialLinearGroup.mapGL ℝ q.out⁻¹) H hε t w hw
  have he : (g * Matrix.SpecialLinearGroup.mapGL ℝ q.out⁻¹) • w = g • (q.out⁻¹ • w) := by
    rw [mul_smul]
    rfl
  rw [he] at hh
  apply hh.trans
  apply pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _))
  apply max_le_max_left
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_mul_of_nonneg_left ((hK ⟨q,rfl⟩).trans (le_max_right _ _)) hε.le

#print axioms exists_cover_cap_inverse

end QuantitativeSpectralExceptionalGeometry
