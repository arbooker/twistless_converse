module

public import FinitenessAllLevelHolomorphicReductionV1
public import FinitenessAllLevelOriginalPencilV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelPencilFredholm

open FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelCompactFredholm FinitenessAllLevelFredholmReduction
  FinitenessAllLevelCertificatePencil QuantitativeArithmeticRetainedCertificate

variable {N Q p : ℕ} {hQ : 0 < Q}

theorem pencil_isFredholm (hN : 0 < N) (A : Certificate N {p} Q hQ) {a b : ℝ}
    (hb : 0 < b) (hab : b < a) (χ : ℕ → ℂ) (m : ℕ) (z : ℂ) :
    (defect (pencil hN A hb hab χ m z)).IsFredholm :=
  isFredholm (pencil_isCompactOperator hN A hb hab χ m z)

theorem pencil_index_zero (hN : 0 < N) (A : Certificate N {p} Q hQ) {a b : ℝ}
    (hb : 0 < b) (hab : b < a) (χ : ℕ → ℂ) (m : ℕ) (z : ℂ) :
    (defect (pencil hN A hb hab χ m z)).index = 0 :=
  index_zero (pencil_isCompactOperator hN A hb hab χ m z)

/-- The actual certificate pencil has a local holomorphic reduction to a
finite-dimensional matrix. The extra Euler and global continuation equations
are not part of this equivalence. -/
theorem pencil_local_reduction (hN : 0 < N) (A : Certificate N {p} Q hQ) {a b : ℝ}
    (hb : 0 < b) (hab : b < a) (χ : ℕ → ℂ) (m : ℕ) (z : ℂ) :
    ∃ P : (defect (pencil hN A hb hab χ m z)).FredholmPackage,
      FiniteDimensional ℂ P.decDom.X₀ ∧ FiniteDimensional ℂ P.decCodom.X₀ ∧
      ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
        AnalyticOnNhd ℂ (fun w => lift P (defect (pencil hN A hb hab χ m w))) U ∧
        AnalyticOnNhd ℂ (fun w => matrix P (defect (pencil hN A hb hab χ m w))) U ∧
        ∀ w ∈ U, ∀ F : space (radius a),
          pencil hN A hb hab χ m w F = F ↔
            ∃ v : P.decDom.X₀,
              matrix P (defect (pencil hN A hb hab χ m w)) v = 0 ∧
              F = lift P (defect (pencil hN A hb hab χ m w)) v := by
  obtain ⟨P⟩ := (pencil_isFredholm hN A hb hab χ m z).nonempty_fredholmPackage
  have hd : Differentiable ℂ (fun w => defect (pencil hN A hb hab χ m w)) :=
    (differentiable_const _).sub (pencil_differentiable hN A hb hab χ m)
  obtain ⟨U, ho, hz, hJ, hM, he⟩ := local_reduction P _ hd rfl
  refine ⟨P, P.decDom.finite_X₀, P.decCodom.finite_X₀, U, ho, hz, hJ, hM, ?_⟩
  intro w hw F
  simpa only [defect_apply, sub_eq_zero, eq_comm (a := F)] using he w hw F

#print axioms pencil_isFredholm
#print axioms pencil_index_zero
#print axioms pencil_local_reduction

end FinitenessAllLevelPencilFredholm
