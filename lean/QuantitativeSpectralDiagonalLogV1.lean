module

public import QuantitativeSpectralLogResolventV1
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection

set_option autoImplicit false
@[expose] public section

namespace QuantitativeSpectralDiagonalLog

variable {A : Type*} [CStarAlgebra A]

/-- Functional calculus on a projection evaluates at its two possible
spectral values. This proves the logarithmic diagonal identity directly. -/
theorem log_two_blocks (P : A) (hp : IsSelfAdjoint P) (hi : IsIdempotentElem P)
    (r s : ℝ) :
    CFC.log (s • (1 : A) + (r-s) • P) =
      Real.log s • (1 : A) + (Real.log r-Real.log s) • P := by
  have hspec : spectrum ℝ P ⊆ ({0,1} : Set ℝ) :=
    (isIdempotentElem_iff_spectrum_subset ℝ P hp).mp hi
  have hfinite : (spectrum ℝ P).Finite := (Set.toFinite {0,1}).subset hspec
  have ha (a b : ℝ) : cfc (fun x : ℝ => b+(a-b)*x) P = b • (1 : A)+(a-b) • P := by
    rw [cfc_const_add b (fun x : ℝ => (a-b)*x) P,
      cfc_const_mul (a-b) (fun x : ℝ => x) P, cfc_id' ℝ P hp,
      Algebra.algebraMap_eq_smul_one]
  rw [← ha r s]
  change cfc Real.log (cfc (fun x : ℝ => s+(r-s)*x) P) = _
  rw [← cfc_comp Real.log (fun x : ℝ => s+(r-s)*x) P hp
    ((hfinite.image _).continuousOn _)]
  rw [← ha (Real.log r) (Real.log s)]
  apply cfc_congr
  intro x hx
  rcases Set.mem_insert_iff.mp (hspec hx) with hzero | hone
  · simp [hzero]
  · have hx1 : x = 1 := Set.mem_singleton_iff.mp hone
    simp [hx1]

/-- The exact trace-log of the two diagonal weights, including the mass of
the final retained projection. -/
theorem trace_log_two_blocks (τ : A →L[ℝ] ℝ)
    (P : A) (hp : IsSelfAdjoint P) (hi : IsIdempotentElem P) (r s : ℝ) :
    τ (CFC.log (s • (1 : A)+(r-s) • P)) =
      τ P * Real.log r + (τ 1-τ P) * Real.log s := by
  rw [log_two_blocks P hp hi, map_add, map_smul, map_smul]
  simp only [smul_eq_mul]
  ring

#print axioms log_two_blocks
#print axioms trace_log_two_blocks

end QuantitativeSpectralDiagonalLog
