module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Topology.Algebra.Order.Archimedean
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public noncomputable section

open Filter Set UpperHalfPlane MeasureTheory
open scoped Topology

/-!
The small-period argument needed for Maass old intersections is topological,
not holomorphic. Accumulating nonzero periods make a continuous function
constant on a real line. On the upper half-plane this gives constancy along
each horocycle, and a vanishing literal horocycle mean then gives zero.
The mean identities also transport vanishing constants through rational
cusp-coordinate changes when both profiles have their actual unit period.

This chapter does not assert that a Hilbert-space spectral vector has a
continuous representative or satisfies the required additional symmetries.
Those physical identifications must be established before using these lemmas
to prove an oldspace intersection formula.
-/

namespace QuantitativeNinaMaass

/-- Nonzero periods approaching zero force a continuous real-line function
to be constant. The target need only be Hausdorff. -/
theorem continuous_constant_of_small_periods {E : Type*}
    [TopologicalSpace E] [T2Space E] (f : ℝ → E) (hf : Continuous f)
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0)) (hne : ∀ n, r n ≠ 0)
    (hperiod : ∀ n, Function.Periodic f (r n)) (x : ℝ) : f x = f 0 := by
  let P : AddSubgroup ℝ :=
    { carrier := {a | Function.Periodic f a}
      zero_mem' := by intro y; simp
      add_mem' := fun ha hb => ha.add_period hb
      neg_mem' := fun ha => ha.neg }
  have hd : Dense (P : Set ℝ) := by
    apply P.dense_of_not_isolated_zero
    intro δ hδ
    have ha : Tendsto (fun n => |r n|) atTop (𝓝 0) := by
      simpa only [abs_zero] using hr.abs
    obtain ⟨n, hn⟩ := (ha.eventually (Iio_mem_nhds hδ)).exists
    refine ⟨|r n|, ?_, abs_pos.mpr (hne n), hn⟩
    rcases le_total 0 (r n) with hnpos | hnneg
    · change Function.Periodic f |r n|
      simpa only [abs_of_nonneg hnpos] using hperiod n
    · change Function.Periodic f |r n|
      simpa only [abs_of_nonpos hnneg] using (hperiod n).neg
  have he : (P : Set ℝ) ⊆ {a | f a = f 0} := by
    intro a ha
    change f a = f 0
    simpa only [zero_add] using ha 0
  exact closure_minimal he (isClosed_eq hf continuous_const) (hd x)

/-- In the Maass setting the conclusion is constancy on each horizontal
horocycle; no Cauchy-Riemann or cusp-decay hypothesis is used. -/
theorem horocycle_constant_of_small_periods (f : ℍ → ℂ) (hf : Continuous f)
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0)) (hne : ∀ n, r n ≠ 0)
    (hperiod : ∀ n z, f (r n +ᵥ z) = f z) (z : ℍ) (x : ℝ) :
    f (x +ᵥ z) = f z := by
  have hc : Continuous (fun a : ℝ => a +ᵥ z) := by
    apply continuous_induced_rng.mpr
    change Continuous (fun a : ℝ => ((a +ᵥ z : ℍ) : ℂ))
    simp only [UpperHalfPlane.coe_vadd]
    exact Complex.continuous_ofReal.add continuous_const
  have hp (n : ℕ) : Function.Periodic (fun a : ℝ => f (a +ᵥ z)) (r n) := by
    intro a
    change f ((a + r n) +ᵥ z) = f (a +ᵥ z)
    rw [add_comm a (r n), add_vadd]
    exact hperiod n (a +ᵥ z)
  simpa only [Function.comp_def, zero_vadd] using
    continuous_constant_of_small_periods _ (hf.comp hc) r hr hne hp x

/-- A literal vanishing horocycle mean eliminates the horizontal constant.
The common-period scale is arbitrary, so this applies to integral cusp
charts using the manuscript's actual level N as common period. -/
theorem continuous_zero_of_small_periods_and_mean (f : ℍ → ℂ)
    (hf : Continuous f) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (hne : ∀ n, r n ≠ 0) (hperiod : ∀ n z, f (r n +ᵥ z) = f z)
    (w : ℝ) (hmean : ∀ z : ℍ, (∫ x in (0 : ℝ)..1, f ((w*x) +ᵥ z)) = 0) :
    f = 0 := by
  funext z
  change f z = 0
  have hz := hmean z
  simp_rw [horocycle_constant_of_small_periods f hf r hr hne hperiod] at hz
  simpa only [intervalIntegral.integral_const, sub_zero, one_smul] using hz

/-- A nonzero integral dilation, including a negative one, preserves the
unit-period mean. This also applies to Banach-valued cusp profiles. -/
theorem periodic_mean_integer_dilate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (hf : Continuous f)
    (hp : Function.Periodic f 1) (m : ℤ) (hm : m ≠ 0) :
    (∫ x in (0 : ℝ)..1, f ((m : ℝ) * x)) = ∫ x in (0 : ℝ)..1, f x := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have he : (∫ x in (0 : ℝ)..(m : ℝ), f x) =
      (m : ℝ) • ∫ x in (0 : ℝ)..1, f x := by
    simpa [Int.cast_smul_eq_zsmul] using
      hp.intervalIntegral_add_zsmul_eq m 0 (fun a b => hf.intervalIntegrable a b)
  rw [intervalIntegral.integral_comp_mul_left f hmR]
  simp only [mul_zero, mul_one, he, smul_smul, inv_mul_cancel₀ hmR, one_smul]

/-- The unit-period mean is independent of the coordinate origin. -/
theorem periodic_mean_translate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (hp : Function.Periodic f 1) (r : ℝ) :
    (∫ x in (0 : ℝ)..1, f (x + r)) = ∫ x in (0 : ℝ)..1, f x := by
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add, add_comm 1 r] using hp.intervalIntegral_add_eq r 0

/-- Rational affine changes preserve the average if both the original
profile and the transported profile have unit period. The second period
comes from actual automorphy; it is not automatic for a rational slope. -/
theorem periodic_mean_rational_affine {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (hf : Continuous f)
    (hp : Function.Periodic f 1) (a d : ℤ) (ha : a ≠ 0) (hd : d ≠ 0) (r : ℝ)
    (htrans : Function.Periodic (fun x => f ((a : ℝ) / d * x + r)) 1) :
    (∫ x in (0 : ℝ)..1, f ((a : ℝ) / d * x + r)) = ∫ x in (0 : ℝ)..1, f x := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have hc : Continuous (fun x : ℝ => f ((a : ℝ) / d * x + r)) := by fun_prop
  have hs : Function.Periodic (fun x : ℝ => f (x + r)) 1 := by
    intro x
    change f (x + 1 + r) = f (x + r)
    rw [show x + 1 + r = x + r + 1 by ring]
    exact hp (x + r)
  calc
    _ = ∫ x in (0 : ℝ)..1, f ((a : ℝ) / d * ((d : ℝ) * x) + r) :=
      (periodic_mean_integer_dilate _ hc htrans d hd).symm
    _ = ∫ x in (0 : ℝ)..1, f ((a : ℝ) * x + r) := by
      congr 1
      funext x
      congr 1
      field_simp
    _ = ∫ x in (0 : ℝ)..1, f (x + r) :=
      periodic_mean_integer_dilate _ (hf.comp (continuous_id.add continuous_const)) hs a ha
    _ = ∫ x in (0 : ℝ)..1, f x := periodic_mean_translate f hp r

#print axioms continuous_constant_of_small_periods
#print axioms horocycle_constant_of_small_periods
#print axioms continuous_zero_of_small_periods_and_mean
#print axioms periodic_mean_integer_dilate
#print axioms periodic_mean_translate
#print axioms periodic_mean_rational_affine

end QuantitativeNinaMaass
