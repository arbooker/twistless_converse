module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace SmallLevelTaylor

open Complex Filter Set Metric MeasureTheory FormalMultilinearSeries
open scoped NNReal ENNReal

/-- Cauchy coefficients on the half-unit circle have a uniform geometric
bound controlled only by the function bound on that circle. -/
theorem cauchy_coefficient_bound {f : ℂ → ℂ} {D : ℝ}
    (hbound : ∀ u : ℂ, ‖u‖≤1/2 → ‖f u‖≤D) (n : ℕ) :
    ‖cauchyPowerSeries f 0 (1/2) n‖≤D*2^n := by
  have hi : (∫ θ : ℝ in 0..2*Real.pi, ‖f (circleMap 0 (1/2) θ)‖)≤D*(2*Real.pi) := by
    apply (le_abs_self _).trans
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun θ : ℝ => ‖f (circleMap 0 (1/2) θ)‖)
      (a := 0) (b := 2*Real.pi) (C := D) (by
        intro θ _
        rw [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
        apply hbound
        simp only [norm_circleMap_zero]
        norm_num)
    simpa only [Real.norm_eq_abs,sub_zero,abs_of_pos Real.two_pi_pos] using h
  calc
    _≤((2*Real.pi)⁻¹*∫ θ : ℝ in 0..2*Real.pi, ‖f (circleMap 0 (1/2) θ)‖)*|(1/2:ℝ)|⁻¹^n :=
      norm_cauchyPowerSeries_le f 0 (1/2) n
    _≤((2*Real.pi)⁻¹*(D*(2*Real.pi)))*|(1/2:ℝ)|⁻¹^n := by
      gcongr
    _=D*2^n := by
      have he : (2*Real.pi)⁻¹*(D*(2*Real.pi))=D := by
        field_simp
      rw [he]
      norm_num

/-- Explicit geometric tail bound, uniform in any family with the same
coefficient bound. This avoids a height-dependent Taylor big-O constant. -/
theorem power_series_tail_bound {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HasFPowerSeriesOnBall f p 0 ((1/2:ℝ≥0):ℝ≥0∞)) {D : ℝ} (hD : 0≤D)
    (hp : ∀ n : ℕ, ‖p n‖≤D*2^n) {u : ℂ} (hu : ‖u‖≤1/4) (M : ℕ) :
    ‖f u-p.partialSum M u‖≤2*D*(2*‖u‖)^M := by
  have hu' : u∈Metric.eball (0:ℂ) ((1/2:ℝ≥0):ℝ≥0∞) := by
    rw [Metric.eball_coe]
    simp only [mem_ball,dist_zero_right,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat]
    linarith
  have hs : HasSum (fun n => p n (fun _ => u)) (f u) := by
    simpa only [zero_add] using hf.hasSum hu'
  have he : f u-p.partialSum M u=∑' n : ℕ, p (n+M) (fun _ => u) := by
    have h := hs.summable.sum_add_tsum_nat_add M
    rw [hs.tsum_eq] at h
    change p.partialSum M u+(∑' n : ℕ, p (n+M) (fun _ => u))=f u at h
    exact (eq_sub_of_add_eq' h).symm
  let q : ℝ := 2*‖u‖
  have hq0 : 0≤q := by dsimp [q]; positivity
  have hqhalf : q≤1/2 := by dsimp [q]; linarith
  have hq1 : q<1 := by linarith
  have hgeo : Summable (fun n : ℕ => q^n) :=
    summable_geometric_of_norm_lt_one (by simpa only [Real.norm_eq_abs,abs_of_nonneg hq0] using hq1)
  have hmajor : Summable (fun n : ℕ => D*q^(n+M)) := by
    simpa only [pow_add,mul_left_comm,mul_assoc,mul_comm] using hgeo.mul_left (D*q^M)
  have hterm (n : ℕ) : ‖p (n+M) (fun _ => u)‖≤D*q^(n+M) := by
    calc
      _≤‖p (n+M)‖*‖u‖^(n+M) := by simpa using (p (n+M)).le_opNorm (fun _ => u)
      _≤(D*2^(n+M))*‖u‖^(n+M) := mul_le_mul_of_nonneg_right (hp _) (by positivity)
      _=D*q^(n+M) := by dsimp [q]; rw [mul_pow]; ring
  have hnorm := Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hmajor
  rw [he]
  calc
    _≤∑' n : ℕ, ‖p (n+M) (fun _ => u)‖ := norm_tsum_le_tsum_norm hnorm
    _≤∑' n : ℕ, D*q^(n+M) := hnorm.tsum_le_tsum hterm hmajor
    _=(D*q^M)/(1-q) := by
      simp_rw [pow_add,show ∀ n : ℕ, D*(q^n*q^M)=(D*q^M)*q^n from fun n => by ring]
      rw [tsum_mul_left,tsum_geometric_of_lt_one hq0 hq1]
      ring
    _≤2*D*q^M := by
      apply (div_le_iff₀ (by linarith : 0<1-q)).mpr
      have hnon : 0≤D*q^M := mul_nonneg hD (pow_nonneg hq0 M)
      nlinarith

theorem cauchy_remainder_bound {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (closedBall 0 (1/2))) {D : ℝ} (hD : 0≤D)
    (hbound : ∀ u : ℂ, ‖u‖≤1/2 → ‖f u‖≤D) {u : ℂ} (hu : ‖u‖≤1/4) (M : ℕ) :
    ‖f u-(cauchyPowerSeries f 0 (1/2)).partialSum M u‖≤2*D*(2*‖u‖)^M := by
  apply power_series_tail_bound (hf.hasFPowerSeriesOnBall (R := (1/2:ℝ≥0)) (by norm_num)) hD
    (cauchy_coefficient_bound hbound) hu M

#print axioms cauchy_coefficient_bound
#print axioms power_series_tail_bound
#print axioms cauchy_remainder_bound

end SmallLevelTaylor
