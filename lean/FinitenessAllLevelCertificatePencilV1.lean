module

public import FinitenessAllLevelCertificateBoundaryV1
public import FinitenessAllLevelBoundaryCoordinatesV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelCertificatePencil

open Complex Metric Set MeasureTheory FinitenessAllLevelDiskSeries FinitenessAllLevelDiskAlgebra
  FinitenessAllLevelBoundaryGeometry FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelCertificateBoundary FinitenessAllLevelCauchyOperator
  QuantitativeArithmeticRetainedCertificate FinitenessAllLevelReconstruction
  FinitenessAllLevelGoodTrace FinitenessAllLevelCauchyTransform

variable {N Q p : ℕ} {hQ : 0 < Q}

def cell (Q : ℕ) (hQ : 0 < Q) (j : Fin Q) : Set ℂ := selector Q hQ ⁻¹' {j}

theorem cell_measurable (Q : ℕ) (hQ : 0 < Q) (j : Fin Q) :
    MeasurableSet (cell Q hQ j) := (selector_measurable Q hQ) (measurableSet_singleton j)

/-- The actual certificate boundary expression, separated into its constant
and linear eigenvalue coefficients and patched by the canonical finite cells. -/
def boundary₀ (hN : 0 < N) (A : Certificate N {p} Q hQ) (r : ℝ) {b : ℝ}
    (hb : 0 < b) (χ : ℕ → ℂ) (m : ℕ) : BoundaryOperator (space r) (radius b) :=
  FinitenessAllLevelBoundarySampling.sum Finset.univ (fun j : Fin Q =>
    cell₀ hN A r (radius_pos b).le hb (cell Q hQ j) (cell_measurable Q hQ j)
      coordinate coordinate_measurable χ m j)

def boundary₁ (A : Certificate N {p} Q hQ) (r b : ℝ)
    (m : ℕ) : BoundaryOperator (space r) (radius b) :=
  FinitenessAllLevelBoundarySampling.sum Finset.univ (fun j : Fin Q =>
    cell₁ A r (radius_pos b).le b (cell Q hQ j) (cell_measurable Q hQ j)
      coordinate coordinate_measurable m j)

/-- At every boundary point, exactly one cell contributes. The resulting
formula is literally the finite two-dilation certificate expression. -/
theorem boundary_formula (hN : 0 < N) (A : Certificate N {p} Q hQ) (r : ℝ) {b : ℝ}
    (hb : 0 < b) (χ : ℕ → ℂ) (m : ℕ) (f : space r) (lam w : ℂ) :
    (boundary₀ hN A r hb χ m).data f w + lam * (boundary₁ A r b m).data f w =
      ∑ i ∈ (A.coeff (selector Q hQ w)).support,
        (A.coeff (selector Q hQ w) i : ℂ) *
          twoDilationRow (lift f) (2 * m) χ (firstMultiplier (fun _ => lam) m)
            (fun q => (q : ℂ) ^ (2 * m)) (selector Q hQ w) (line (coordinate w) b) i := by
  classical
  simp only [boundary₀, boundary₁, FinitenessAllLevelBoundarySampling.sum_apply,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [Finset.sum_eq_single (selector Q hQ w)]
  · exact cell_formula hN A r (radius_pos b).le hb _ (cell_measurable Q hQ _)
      coordinate coordinate_measurable χ m _ f lam w rfl
  · intro j _ hj
    have hw : w ∉ cell Q hQ j := by
      change selector Q hQ w ≠ j
      exact Ne.symm hj
    obtain ⟨h0, h1⟩ := cell_outside hN A r (radius_pos b).le hb _
      (cell_measurable Q hQ j) coordinate coordinate_measurable χ m j f w hw
    rw [h0, h1, mul_zero, add_zero]
  · simp

theorem radius_strictAnti {a b : ℝ} (hab : b < a) : radius a < radius b := by
  apply Real.exp_lt_exp.mpr
  have hp := Real.pi_pos
  nlinarith

/-- The compact affine reconstruction pencil is now constructed from the
actual certificate coefficients and Fricke/dilation source maps. The next
bridge must establish its fixed-point property for original solutions using
the certificate's strict upward-height estimates. -/
def pencil (hN : 0 < N) (A : Certificate N {p} Q hQ) {a b : ℝ}
    (hb : 0 < b) (hab : b < a) (χ : ℕ → ℂ) (m : ℕ) (lam : ℂ) :
    space (radius a) →L[ℂ] space (radius a) :=
  FinitenessAllLevelCauchyOperator.pencil (radius_pos a).le (radius_strictAnti hab)
    (boundary₀ hN A (radius a) hb χ m) (boundary₁ A (radius a) b m) lam

theorem pencil_isCompactOperator (hN : 0 < N) (A : Certificate N {p} Q hQ) {a b : ℝ}
    (hb : 0 < b) (hab : b < a) (χ : ℕ → ℂ) (m : ℕ) (lam : ℂ) :
    IsCompactOperator (pencil hN A hb hab χ m lam) :=
  FinitenessAllLevelCauchyOperator.pencil_isCompactOperator _ _ _ _ _

theorem pencil_differentiable (hN : 0 < N) (A : Certificate N {p} Q hQ) {a b : ℝ}
    (hb : 0 < b) (hab : b < a) (χ : ℕ → ℂ) (m : ℕ) :
    Differentiable ℂ (pencil hN A hb hab χ m) :=
  FinitenessAllLevelCauchyOperator.pencil_differentiable _ _ _ _

theorem pencil_apply (hN : 0 < N) (A : Certificate N {p} Q hQ) {a b : ℝ}
    (hb : 0 < b) (hab : b < a) (χ : ℕ → ℂ) (m : ℕ) (lam : ℂ)
    (f : space (radius a)) (z : Disk (radius a)) :
    (pencil hN A hb hab χ m lam f).val z =
      positive (radius b)
        ((boundary₀ hN A (radius a) hb χ m).data f +
          lam • (boundary₁ A (radius a) b m).data f) z.val := by
  change positive (radius b) ((boundary₀ hN A (radius a) hb χ m).data f) z.val +
      lam • positive (radius b) ((boundary₁ A (radius a) b m).data f) z.val = _
  rw [positive_add (radius_pos b) ((boundary₀ hN A (radius a) hb χ m).integrable f)
    (((boundary₁ A (radius a) b m).integrable f).const_smul (a := lam))
    (closedBall_subset_ball (radius_strictAnti hab) z.property), positive_smul]

#print axioms boundary_formula
#print axioms pencil_isCompactOperator
#print axioms pencil_differentiable
#print axioms pencil_apply

end FinitenessAllLevelCertificatePencil
