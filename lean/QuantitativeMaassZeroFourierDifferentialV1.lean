module

public import QuantitativeMaassHeckeConstantV1
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped Interval Topology

namespace QuantitativeMaass

/-- Differentiation of the actual horocycle integral. Joint continuity on
compact rectangles supplies the domination; no integral-derivative identity
is included among the hypotheses. -/
theorem hasDerivAt_zeroFourier (F Fy : ℝ → ℝ → ℂ)
    (hF : Continuous (Function.uncurry F)) (hFy : Continuous (Function.uncurry Fy))
    (hd : ∀ x y, HasDerivAt (F x) (Fy x y) y) (y : ℝ) :
    HasDerivAt (zeroFourier F) (zeroFourier Fy y) y := by
  obtain ⟨K,hK⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := Icc (0:ℝ) 1 ×ˢ Icc (y-1) (y+1)) hFy.continuousOn
  have hc (v : ℝ) : Continuous (fun x => F x v) := hF.comp (continuous_id.prodMk continuous_const)
  have hdc (v : ℝ) : Continuous (fun x => Fy x v) := hFy.comp (continuous_id.prodMk continuous_const)
  have hi := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun v x => F x v) (F' := fun v x => Fy x v)
    (μ := volume) (a := (0:ℝ)) (b := 1) (bound := fun _ => K)
    (s := Ioo (y-1) (y+1)) (x₀ := y)
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall fun v => (hc v).aestronglyMeasurable)
    ((hc y).intervalIntegrable _ _) (hdc y).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x hx v hv => hK (x,v)
      ⟨⟨(show 0<x from (by simpa using hx.1)).le,by simpa using hx.2⟩,
        ⟨hv.1.le,hv.2.le⟩⟩)
    (continuous_const.intervalIntegrable _ _)
    (Filter.Eventually.of_forall fun x _ v _ => hd x v)
  exact hi.2

theorem zeroFourier_secondVertical (F Fy Fyy : ℝ → ℝ → ℂ)
    (hF : Continuous (Function.uncurry F)) (hFy : Continuous (Function.uncurry Fy))
    (hFyy : Continuous (Function.uncurry Fyy))
    (hd : ∀ x y, HasDerivAt (F x) (Fy x y) y)
    (hdd : ∀ x y, HasDerivAt (Fy x) (Fyy x y) y) (y : ℝ) :
    deriv (deriv (zeroFourier F)) y=zeroFourier Fyy y := by
  have he : deriv (zeroFourier F)=zeroFourier Fy := by
    funext v
    exact (hasDerivAt_zeroFourier F Fy hF hFy hd v).deriv
  rw [he]
  exact (hasDerivAt_zeroFourier Fy Fyy hFy hFyy hdd y).deriv

theorem periodic_deriv (f : ℝ → ℂ) (T : ℝ) (hf : Function.Periodic f T) :
    Function.Periodic (deriv f) T := by
  intro x
  rw [←deriv_comp_add_const]
  congr 1
  exact funext hf

/-- The horizontal second derivative integrates to zero because the first
derivative is itself periodic. This is the missing boundary cancellation
in the zero-channel Laplacian calculation. -/
theorem periodic_secondDerivative_average_zero (f : ℝ → ℂ)
    (hperiod : Function.Periodic f 1) (hd : Differentiable ℝ (deriv f))
    (hdd : Continuous (deriv (deriv f))) :
    (∫ x in (0:ℝ)..1, deriv (deriv f) x)=0 := by
  rw [intervalIntegral.integral_deriv_eq_sub (fun x _ => hd x)
    (hdd.intervalIntegrable _ _)]
  have he := periodic_deriv f 1 hperiod 0
  simpa using sub_eq_zero.mpr he

#print axioms hasDerivAt_zeroFourier
#print axioms zeroFourier_secondVertical
#print axioms periodic_secondDerivative_average_zero

end QuantitativeMaass
