module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open ContinuousLinearMap MeasureTheory

namespace QuantitativeMaass

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Pulling a cogram back through the same change of metric cancels that
change exactly. No estimate by the norm of the metric is needed. -/
theorem metric_cogram_cancel (M : H ≃L[ℂ] H) (W : E →L[ℂ] H)
    (K : H →L[ℂ] H) :
    let J := M.toContinuousLinearMap.comp W
    let L := K.comp M.symm.toContinuousLinearMap
    L.comp ((J.comp J.adjoint).comp L.adjoint) =
      (K.comp W).comp (K.comp W).adjoint := by
  intro J L
  have hcancel : L.comp J = K.comp W := by
    ext x
    change K (M.symm (M (W x))) = K (W x)
    rw [M.symm_apply_apply]
  calc
    _ = (L.comp J).comp (L.comp J).adjoint := by
      simp only [adjoint_comp, comp_assoc]
    _ = _ := by rw [hcancel]

/-- The scalar density of a pulled-back cogram is the exact source energy.
This identity does not cyclically rearrange an infinite operator trace. -/
theorem metric_cogram_energy (M : H ≃L[ℂ] H) (W : E →L[ℂ] H)
    (K : H →L[ℂ] H) (x : H) :
    let J := M.toContinuousLinearMap.comp W
    let L := K.comp M.symm.toContinuousLinearMap
    (inner ℂ (L.comp ((J.comp J.adjoint).comp L.adjoint) x) x).re =
      ‖W.adjoint (K.adjoint x)‖ ^ 2 := by
  dsimp only
  rw [metric_cogram_cancel]
  change (inner ℂ ((K.comp W) ((K.comp W).adjoint x)) x).re = _
  rw [← (K.comp W).adjoint_inner_right]
  simpa only [adjoint_comp, comp_apply, RCLike.re_eq_complex_re] using
    (norm_sq_eq_re_inner (𝕜 := ℂ) ((K.comp W).adjoint x)).symm

/-- The cancellation also holds for localized columns over any measure.
Finiteness of the integral is a separate analytic issue. -/
theorem metric_cogram_column_integral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (c : α → H) (M : H ≃L[ℂ] H)
    (W : E →L[ℂ] H) (K : H →L[ℂ] H) :
    let J := M.toContinuousLinearMap.comp W
    let L := K.comp M.symm.toContinuousLinearMap
    (∫ x, (inner ℂ (L.comp ((J.comp J.adjoint).comp L.adjoint) (c x)) (c x)).re ∂μ) =
      ∫ x, ‖W.adjoint (K.adjoint (c x))‖ ^ 2 ∂μ := by
  intro J L
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => metric_cogram_energy M W K (c x))

#print axioms metric_cogram_cancel
#print axioms metric_cogram_energy
#print axioms metric_cogram_column_integral

end QuantitativeMaass
