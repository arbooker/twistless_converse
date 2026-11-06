module

public import QuantitativeSpectralExceptionalRowsV1
public import QuantitativeSpectralObservabilityCoverV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalWide

open MeasureTheory UpperHalfPlane ContinuousLinearMap AsymptoticRegularTrace
open AsymptoticObservationStack QuantitativeSpectralExceptionalRows
open QuantitativeSpectralObservability
open scoped lp ENNReal MatrixGroups

abbrev G := AsymptoticRationalGroup.Group
abbrev Space := ℓ²(G,ℂ)

variable {ι : Type*}

/-- The actual exceptional row for the three-unit reduction cover. -/
def boundary (N : ℕ) (H C : ℝ) (T : ℍ → ι → Space →L[ℂ] Space)
    (x : ℍ) (i : ι) : Space →L[ℂ] Space :=
  omitted (wideTailCover N (H/C)) (fun y => T y i) x

def interior (N : ℕ) (H C : ℝ) (T : ℍ → ι → Space →L[ℂ] Space)
    (x : ℍ) (i : ι) : Space →L[ℂ] Space :=
  retained (wideTailCover N (H/C)) (fun y => T y i) x

theorem row_factorization (N : ℕ) (H C : ℝ) (T : ℍ → ι → Space →L[ℂ] Space)
    (x : ℍ) (i : ι) : T x i = interior N H C T x i + boundary N H C T x i :=
  (retained_add_omitted (wideTailCover N (H/C)) (fun y => T y i) x).symm

theorem stack_factorization [Fintype ι] (N : ℕ) (H C : ℝ) (T : ℍ → ι → Space →L[ℂ] Space)
    (x : ℍ) : stack (T x) = stack (interior N H C T x) + stack (boundary N H C T x) := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  exact congrArg (fun B : Space →L[ℂ] Space => B v) (row_factorization N H C T x i)

theorem boundary_regular (N : ℕ) (hN : 0 < N) (H C : ℝ)
    (T : ℍ → ι → Space →L[ℂ] Space)
    (hm : ∀ i g h, Measurable (fun x => matrix (T x i) g h))
    (hc : ∀ i, Covariant (fun x => T x i)) (i : ι) :
    (∀ g h, Measurable (fun x => matrix (boundary N H C T x i) g h)) ∧
      Covariant (fun x => boundary N H C T x i) :=
  omitted_regular (fun g => (AsymptoticRationalGroup.measurePreserving g).measurable)
    (wideTailCover_measurable N hN (H/C)) _ (hm i) (hc i)

theorem boundary_output_le (N : ℕ) (H C : ℝ)
    (T : ℍ → ι → Space →L[ℂ] Space) (x : ℍ) (i : ι) :
    AsymptoticPolarIsometry.outputSpace (boundary N H C T x i) ≤
      AsymptoticOrbitRegion.Space (wideTailCover N (H/C)) x :=
  omitted_output_le _ _ _

/-- The genuine polar source-rank of the exceptional finite-row map,
with the explicit three-unit-width cusp constant. -/
theorem boundary_stack_rank [Fintype ι] (N : ℕ) (hN : 0 < N) {H C : ℝ} (hH : 0 < H) (hC : 0 < C)
    (T : ℍ → ι → Space →L[ℂ] Space)
    (hm : ∀ i g h, Measurable (fun x => matrix (T x i) g h))
    (hc : ∀ i, Covariant (fun x => T x i))
    (M : ι → ℝ) (hM0 : ∀ i, 0 ≤ M i) (hM : ∀ x i, ‖T x i‖ ≤ M i) :
    trace volume (fun x => (stack (boundary N H C T x)).kerᗮ.starProjection) ≤
      (Fintype.card ι : ℝ≥0∞) *
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ CongruenceSubgroup.Gamma0 N) : ℝ≥0∞) *
          (3 * ENNReal.ofReal (C/H)) := by
  have hr := omitted_stack_rank_le_area volume AsymptoticRationalGroup.measurePreserving
    (wideTailCover_measurable N hN (H/C)) T hm hc M hM0 hM
  apply hr.trans
  have ht := wideTailCover_area N hN (div_pos hH hC)
  rw [inv_div] at ht
  exact (mul_le_mul_right ht (Fintype.card ι : ℝ≥0∞)).trans_eq (mul_assoc _ _ _).symm

#print axioms row_factorization
#print axioms stack_factorization
#print axioms boundary_output_le
#print axioms boundary_stack_rank

end QuantitativeSpectralExceptionalWide
