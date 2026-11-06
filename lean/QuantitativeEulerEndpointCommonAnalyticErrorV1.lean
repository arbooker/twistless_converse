module

public import QuantitativeEulerEndpointActualTerminalSectorBoundV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointCommonReconstruction
open FinitenessCertificate FinitenessGlobalHeight QuantitativeHolomorphic QuantitativeHolomorphic.Schedule
open AsymptoticCylinderModeComparison

/-- The common accuracy has at most reciprocal-horizon reconstruction error. -/
theorem scheduled_exp_error {K R : ℝ} (hK : 0≤K) (hR : 1≤R) :
    Real.exp (-3*Real.exp ((K+1)*R))≤1/R := by
  have hR0 : 0<R := by linarith
  have hs : R≤Real.exp ((K+1)*R) := by
    have hh := Real.add_one_le_exp ((K+1)*R)
    nlinarith
  have he : Real.exp (-3*Real.exp ((K+1)*R))≤Real.exp (-R) :=
    Real.exp_le_exp.mpr (by linarith)
  apply he.trans
  rw [Real.exp_neg,one_div]
  exact (inv_le_inv₀ (Real.exp_pos R) hR0).mpr (by linarith [Real.add_one_le_exp R])

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

/-- The actual reconstruction, upper-tail, and weighted-mode errors have
reciprocal-horizon decay plus a double-exponential coefficient over sqrt(weight).
Both constants precede horizon and weight. -/
theorem exists_horizon_analytic_error {K : ℝ} (hK : 0≤K) :
    ∃ C D : ℝ,0≤C ∧ 0≤D ∧ ∀ n h : ℕ,
      let s := Real.exp ((K+1)*(4:ℝ)^n)
      retainedTraceError A P s h+weightedTraceError A P s h≤
        C/(4:ℝ)^n+2*Real.exp (Real.exp (D*(4:ℝ)^n))*(Real.sqrt (2*h+2:ℝ))⁻¹ := by
  let c := 2*traceRateConstant A P+upperScheduledHeightConstant A P 0
  let b := sharpGrowthConstant A P 0*upperWeightCoefficient (fixedMajorant A P)
  let d := 2*lowerModeCoefficient A P+abs (lowerInverseGrowthConstant A P 0)
  let D := abs b+abs d+4*(K+1)+1
  refine ⟨abs c,D,abs_nonneg _,by dsimp only [D]; positivity,?_⟩
  intro n h s
  let R : ℝ := (4:ℝ)^n
  let E := Real.exp (Real.exp (D*R))
  have hR : 1≤R := one_le_pow₀ (by norm_num)
  have hR0 : 0≤R := by linarith
  have he : s^4=Real.exp ((4*(K+1))*R) := by
    dsimp only [s,R]
    rw [←Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hcommon (t : ℝ) (ht : abs t+4*(K+1)≤D) : t*s^4≤Real.exp (D*R) := by
    apply (mul_le_mul_of_nonneg_right (le_abs_self t) (pow_nonneg (Real.exp_pos _).le 4)).trans
    rw [he]
    apply (QuantitativeEulerEndpointPolynomialGrowth.scaled_exp_le (abs_nonneg t) hR).trans
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ht hR0)
  have hb : b*s^4≤E := by
    have hh := hcommon b (by dsimp only [D]; linarith [abs_nonneg d])
    exact hh.trans (by dsimp only [E]; linarith [Real.add_one_le_exp (Real.exp (D*R))])
  have hd : Real.exp (d*s^4)≤E :=
    Real.exp_le_exp.mpr (hcommon d (by dsimp only [D]; linarith [abs_nonneg b]))
  have hc : c*Real.exp (-3*s)≤abs c/R := by
    apply (mul_le_mul_of_nonneg_right (le_abs_self c) (Real.exp_pos _).le).trans
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left (scheduled_exp_error hK hR) (abs_nonneg c)
  have hi : 0≤(Real.sqrt (2*h+2:ℝ))⁻¹ := by positivity
  have hh := add_le_add (mul_le_mul_of_nonneg_right hb hi) (mul_le_mul_of_nonneg_right hd hi)
  change c*Real.exp (-3*s)+(b*s^4)*(Real.sqrt (2*h+2:ℝ))⁻¹+
    Real.exp (d*s^4)*(Real.sqrt (2*h+2:ℝ))⁻¹≤_
  nlinarith only [hc,hh]

#print axioms scheduled_exp_error
#print axioms exists_horizon_analytic_error
end QuantitativeEulerEndpointCommonReconstruction
