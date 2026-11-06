module

public import SmallLevelTaylorFrickeV1
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace SmallLevelTaylor

open Complex Filter Set Metric MeasureTheory FinitenessPolynomialSeries FinitenessFourierConstruction
open scoped Topology

theorem half_circle_norm (θ : ℝ) : ‖circleMap 0 (1/2) θ‖=(1:ℝ)/2 := by
  rw [norm_circleMap_zero]
  norm_num

theorem half_circle_ne_zero (θ : ℝ) : circleMap 0 (1/2) θ≠0 := by
  apply norm_pos_iff.mp
  rw [half_circle_norm]
  norm_num

theorem deformed_circle_continuous (k : ℕ) {a : ℕ → ℂ} (ha : PolynomialBound a)
    (β : ℝ) {c : ℝ} (hc : 0<c) :
    Continuous (fun p : (Ioi (0:ℝ))×ℝ =>
      deformed k a β c p.1 (circleMap 0 (1/2) p.2)) := by
  have hu (θ : ℝ) : ‖circleMap 0 (1/2) θ‖≤1/2 := (half_circle_norm θ).le
  have hpoint : Continuous (fun p : (Ioi (0:ℝ))×ℝ =>
      deformPoint β c p.1 (circleMap 0 (1/2) p.2)) := by
    unfold deformPoint
    fun_prop (disch := intro p; exact one_add_ne_zero (hu p.2))
  have hfourier : Continuous (fun p : (Ioi (0:ℝ))×ℝ =>
      fourier a (deformPoint β c p.1 (circleMap 0 (1/2) p.2))) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (FinitenessFourierConstruction.holomorphic ha
      (deformPoint_positive β hc p.1.property (hu p.2))).continuousAt.comp
        (f := fun p : (Ioi (0:ℝ))×ℝ => deformPoint β c p.1 (circleMap 0 (1/2) p.2)) hpoint.continuousAt
  unfold deformed
  apply Continuous.mul _ hfourier
  fun_prop (disch := intro p; exact pow_ne_zero k (one_add_ne_zero (hu p.2)))

theorem cauchy_term_continuous (k : ℕ) {a : ℕ → ℂ} (ha : PolynomialBound a)
    (β r : ℝ) {c : ℝ} (hc : 0<c) (n : ℕ) :
    ContinuousOn (fun y : ℝ =>
      cauchyPowerSeries (deformed k a β c y) 0 (1/2) n (fun _ => ((y/r:ℝ):ℂ)*I)) (Ioi 0) := by
  rw [continuousOn_iff_continuous_domRestrict]
  simp only [Set.domRestrict_def,cauchyPowerSeries_apply,sub_zero,circleIntegral,smul_eq_mul]
  apply Continuous.const_mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  have hquot : Continuous (fun p : (Ioi (0:ℝ))×ℝ =>
      (((p.1:ℝ)/r:ℝ):ℂ)*I/circleMap 0 (1/2) p.2) := by
    fun_prop (disch := intro p; exact half_circle_ne_zero p.2)
  have hinv : Continuous (fun p : (Ioi (0:ℝ))×ℝ => (circleMap 0 (1/2) p.2)⁻¹) := by
    fun_prop (disch := intro p; exact half_circle_ne_zero p.2)
  have hd : Continuous (fun p : (Ioi (0:ℝ))×ℝ => deriv (circleMap 0 (1/2)) p.2) := by
    simp_rw [deriv_circleMap]
    fun_prop
  exact hd.mul ((hquot.pow n).mul (hinv.mul (deformed_circle_continuous k ha β hc)))

theorem frickeTaylorPolynomial_continuous (k : ℕ) {a : ℕ → ℂ} (ha : PolynomialBound a)
    {L r : ℝ} (hL : 0<L) (hr : r≠0) (M : ℕ) :
    ContinuousOn (frickeTaylorPolynomial k a L r M) (Ioi 0) := by
  unfold frickeTaylorPolynomial FormalMultilinearSeries.partialSum
  apply continuousOn_finsetSum
  intro n _
  exact cauchy_term_continuous k ha (-1/(L*r)) r (mul_pos hL (sq_pos_of_ne_zero hr)) n

theorem fricke_error_locallyIntegrable (k : ℕ) {a : ℕ → ℂ} (ha : PolynomialBound a)
    {L r : ℝ} (hL : 0<L) (hr : r≠0) (χ : ℂ) (M : ℕ) :
    LocallyIntegrableOn (fun y : ℝ => fourier a ((r:ℂ)+(y:ℂ)*I)-
      (χ/(((Real.sqrt L:ℂ)*(r:ℂ))^k))*frickeTaylorPolynomial k a L r M y) (Ioi 0) := by
  have hf : ContinuousOn (fun y : ℝ => fourier a ((r:ℂ)+(y:ℂ)*I)) (Ioi 0) := by
    intro y hy
    exact ((FinitenessFourierConstruction.holomorphic ha (by simpa using hy)).continuousAt.comp
      (by fun_prop)).continuousWithinAt
  exact (hf.sub ((frickeTaylorPolynomial_continuous k ha hL hr M).const_mul _)).locallyIntegrableOn measurableSet_Ioi

#print axioms deformed_circle_continuous
#print axioms cauchy_term_continuous
#print axioms frickeTaylorPolynomial_continuous
#print axioms fricke_error_locallyIntegrable

end SmallLevelTaylor
