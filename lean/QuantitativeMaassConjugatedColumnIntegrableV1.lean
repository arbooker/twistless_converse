module

public import QuantitativeMaassConjugatedColumnBoundV1
public import Mathlib.MeasureTheory.Function.Floor

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory ContinuousLinearMap

namespace QuantitativeMaass.LogBands

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (l : α → ℝ) (hl : Measurable l)

/-- The inverse row depends measurably on the integer output band, even
when the inverse weight is unbounded on the whole space. -/
theorem rowInverseSum_adjoint_stronglyMeasurable (J : ℕ) :
    StronglyMeasurable (fun x => (rowInverseSum μ l hl J ⌊l x⌋).adjoint) := by
  have hd : StronglyMeasurable (fun n : ℤ => (rowInverseSum μ l hl J n).adjoint) :=
    StronglyMeasurable.of_discrete
  exact hd.comp_measurable (Int.measurable_floor.comp hl)

/-- Finite-band conjugation preserves strong measurability of a column
with respect to any output measure. -/
theorem conjugatedColumn_aestronglyMeasurable (ν : Measure α)
    (c : α → Lp ℂ 2 μ) (hc : AEStronglyMeasurable c ν) (J : ℕ) :
    AEStronglyMeasurable (conjugatedColumn μ l hl c J) ν := by
  have hw : StronglyMeasurable (fun x => (Real.exp (l x) : ℂ)) :=
    (Complex.continuous_ofReal.comp_stronglyMeasurable (hl.exp.stronglyMeasurable))
  have heval : Continuous (fun p :
      (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) × Lp ℂ 2 μ => p.1 p.2) := by fun_prop
  exact heval.comp_aestronglyMeasurable
    ((rowInverseSum_adjoint_stronglyMeasurable μ l hl J).aestronglyMeasurable.prodMk
      (hw.aestronglyMeasurable.smul hc))

theorem conjugatedColumn_norm_bound (c : α → Lp ℂ 2 μ) (J : ℕ) (x : α) :
    ‖conjugatedColumn μ l hl c J x‖ ≤
      (((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1))*‖c x‖ := by
  simpa only [conjugatedColumn, smul_zero, map_zero, sub_zero] using
    conjugatedColumn_sub_bound μ l hl c (fun _ => 0) J x

/-- An actual square-integrable column remains square integrable after
finite-band conjugation; no global inverse-weight bound is assumed. -/
theorem conjugatedColumn_memLp (ν : Measure α)
    (c : α → Lp ℂ 2 μ) (hc : MemLp c 2 ν) (J : ℕ) :
    MemLp (conjugatedColumn μ l hl c J) 2 ν := by
  apply hc.of_le_mul (conjugatedColumn_aestronglyMeasurable μ l hl ν c hc.aestronglyMeasurable J)
  exact Filter.Eventually.of_forall (conjugatedColumn_norm_bound μ l hl c J)

#print axioms rowInverseSum_adjoint_stronglyMeasurable
#print axioms conjugatedColumn_aestronglyMeasurable
#print axioms conjugatedColumn_norm_bound
#print axioms conjugatedColumn_memLp

end QuantitativeMaass.LogBands
