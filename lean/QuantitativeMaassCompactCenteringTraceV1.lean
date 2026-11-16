module

public import QuantitativeMaassCompactMeanEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticClassicalPetersson
open scoped SchwartzMap
namespace QuantitativeMaass

private theorem positive_quadratic_sub_le {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (T : V→L[ℂ]V) (hT : T.IsPositive) (x y : V) :
    (inner ℂ (T (x-y)) (x-y)).re≤
      2*(inner ℂ (T x) x).re+2*(inner ℂ (T y) y).re := by
  have hh := hT.re_inner_nonneg_left (x+y)
  change 0≤(inner ℂ (T (x+y)) (x+y)).re at hh
  simp only [map_add,inner_add_left,inner_add_right,Complex.add_re] at hh
  simp only [map_sub,inner_sub_left,inner_sub_right,Complex.sub_re]
  linarith

/-- A positive trace permits removal of a mean with a controlled additive
energy error. No commutation of the operator and the mean is required. -/
theorem columnLinearTrace_sub_le {α V : Type*} [MeasurableSpace α]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (μ : Measure α) (c d : α→V) (hc : MemLp c 2 μ) (hd : MemLp d 2 μ)
    (T : V→L[ℂ]V) (hT : T.IsPositive) :
    columnLinearTrace μ (fun z => c z-d z) T≤
      2*columnLinearTrace μ c T+2*‖T‖*(∫ z,‖d z‖^2 ∂μ) := by
  have hi := (memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).mp hd
  have hpoint (z : α) : (inner ℂ (T (c z-d z)) (c z-d z)).re≤
      2*(inner ℂ (T (c z)) (c z)).re+(2*‖T‖)*‖d z‖^2 := by
    have hb := (le_abs_self _).trans (linearPacketTrace_column_bound T (d z))
    have hh := positive_quadratic_sub_le T hT (c z) (d z)
    linarith
  have hh := integral_mono_ae (columnLinearTrace_integrable μ _ (hc.sub hd) T)
    (((columnLinearTrace_integrable μ c hc T).const_mul 2).add (hi.const_mul (2*‖T‖)))
    (Eventually.of_forall hpoint)
  simp only [Pi.add_apply,Pi.sub_apply] at hh
  rw [integral_add ((columnLinearTrace_integrable μ c hc T).const_mul 2) (hi.const_mul (2*‖T‖)),
    integral_const_mul,integral_const_mul] at hh
  exact hh

/-- The compact-input trace of the actual centered packet is bounded by
its uncentered trace and an explicit off-diagonal-amplitude error. -/
theorem compact_input_centered_trace_uncenter
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    {a : ℝ} (ha : 0<a) (b : ℝ) (C : ℝ) (hC : 0≤C)
    (hb : ∀ d : ℝ,0<d →
      ‖abelProfile (evenCoshLift (timeConvolution f f)) (Real.cosh d)‖≤C/Real.sqrt (Real.sinh d))
    (T : Lp ℂ 2 (quotientMeasure 0)→L[ℂ]Lp ℂ 2 (quotientMeasure 0)) (hT : T.IsPositive) :
    let P := AsymptoticRegionL2.projection (quotientMeasure 0) (upperRectangle 0 1 a b)
      (upperRectangle_compact _ _ _ _ ha).measurableSet
    let K := upperRectangle 0 1 (a*Real.exp (-R)) (b*Real.exp R)
    columnLinearTrace (quotientMeasure 0)
      (fun z => P (cylinderCenteredTimeColumn f hc he R hR hs z)) T≤
      2*columnLinearTrace (quotientMeasure 0)
        (fun z => P (cylinderTimeColumn f hc he R hR hs z)) T+
      2*‖T‖*(max 0 (b*Real.exp R)*
        (C*(Real.pi*(2*(2*(|Real.cosh (2*R)|+1)+1)+2)))*volume.real K) := by
  intro P K
  let c := fun z => P (cylinderTimeColumn f hc he R hR hs z)
  let cc := fun z => P (cylinderCenteredTimeColumn f hc he R hR hs z)
  have hcu : MemLp c 2 (quotientMeasure 0) := cylinderTimeColumn_compact_input_memLp f hc he R hR hs ha b
  have hcc : MemLp cc 2 (quotientMeasure 0) := cylinderCenteredTimeColumn_compact_input_memLp f hc he R hR hs ha b
  have hh := columnLinearTrace_sub_le (quotientMeasure 0) c (fun z => c z-cc z) hcu (hcu.sub hcc) T hT
  have heq : (fun z => c z-(c z-cc z))=cc := by funext z; abel
  rw [heq] at hh
  have hmean := mul_le_mul_of_nonneg_left
    (compact_input_column_mean_energy f hc he R hR hs hr ha b C hC hb)
    (by positivity : 0≤2*‖T‖)
  exact hh.trans (add_le_add le_rfl hmean)

#print axioms columnLinearTrace_sub_le
#print axioms compact_input_centered_trace_uncenter
end QuantitativeMaass
