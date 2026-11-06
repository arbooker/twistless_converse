module

public import QuantitativeArithmeticRetainedGrowingEnvelopeV1
public import QuantitativeHolomorphicGrowingApproximationV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedApproximationSchedule
open QuantitativeArithmeticEnvelope
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedFiniteNormalization QuantitativeArithmeticRetainedFilterTrace
open QuantitativeArithmeticRetainedCylinderNormalization (gramLower gramLower_le_one gramLower_pos bound bound_one_le)
open QuantitativeArithmeticRetainedScheduleGrowth (accuracy iterations newton_growth)

/-- Allocate the requested filter error over its actual polynomial degree. -/
def tolerance (s : ℝ) (d : ℕ) : ℝ := Real.exp (-8*s)/(2*d+2:ℝ)
def logAccuracy (s : ℝ) (d : ℕ) : ℝ := 8*s+Real.log (2*d+2:ℝ)

theorem tolerance_pos (s : ℝ) (d : ℕ) : 0<tolerance s d := by unfold tolerance; positivity

theorem tolerance_eq (s : ℝ) (d : ℕ) : tolerance s d=accuracy (logAccuracy s d) := by
  have hp : 0<(2*d+2:ℝ) := by positivity
  unfold tolerance accuracy logAccuracy
  calc
    _ = Real.exp (-8*s)*Real.exp (-Real.log (2*d+2:ℝ)) := by
      rw [Real.exp_neg,Real.exp_log hp,div_eq_mul_inv]
    _ = _ := by rw [←Real.exp_add]; congr 1; ring

theorem logAccuracy_bounds {C s : ℝ} (hC : 0≤C) (hs : 1≤s) (d : ℕ)
    (hd : (d:ℝ)≤Real.exp (C*s^2)) :
    1≤logAccuracy s d ∧ logAccuracy s d≤(8+Real.log 4+C)*s^2 := by
  have hD : 0<(2*d+2:ℝ) := by positivity
  have hD1 : 1≤(2*d+2:ℝ) := by nlinarith [Nat.cast_nonneg (α:=ℝ) d]
  have he : 1≤Real.exp (C*s^2) := Real.one_le_exp (by positivity)
  have hde : (2*d+2:ℝ)≤4*Real.exp (C*s^2) := by linarith
  have hl := Real.log_le_log hD hde
  rw [Real.log_mul (by norm_num : (4:ℝ)≠0) (Real.exp_ne_zero _),Real.log_exp] at hl
  have hl0 := Real.log_nonneg hD1
  have hc0 : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  dsimp only [logAccuracy]
  constructor
  · linarith
  · have hs2 : 1≤s^2 := by nlinarith
    have hss : s≤s^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hs2 hc0]

theorem logAccuracy_growth (d : ℝ → ℕ) (hd : Exp 2 (fun s => (d s:ℝ))) :
    Poly 2 (fun s => logAccuracy s (d s)) ∧ ∀s : ℝ,1≤s → 1≤logAccuracy s (d s) := by
  obtain ⟨C,hC,hc⟩ := hd
  refine ⟨⟨8+Real.log 4+C,?_,fun s hs => (logAccuracy_bounds hC hs (d s) (hc s hs)).2⟩,
    fun s hs => (logAccuracy_bounds hC hs (d s) (hc s hs)).1⟩
  have := Real.log_nonneg (by norm_num : (1:ℝ)≤4)
  linarith

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ) (P : Parameters A)

theorem filter_error_bounds (s : ℝ) (d : ℕ) :
    0<traceError A P (rawTolerance A P (tolerance s d)) (lowerHeight A P (tolerance s d))
      (newtonDepth A P (tolerance s d)) d ∧
    traceError A P (rawTolerance A P (tolerance s d)) (lowerHeight A P (tolerance s d))
      (newtonDepth A P (tolerance s d)) d≤Real.exp (-8*s) := by
  have ht := tolerance_pos s d
  have hraw := rawTolerance_pos A P ht
  have hy := lowerHeight_pos A P ht
  have hε := P.epsilon_pos
  have hb : 0<bound A P := zero_lt_one.trans_le (bound_one_le A P)
  have hc : 0≤1-gramLower A P := sub_nonneg.mpr (gramLower_le_one A P)
  constructor
  · unfold traceError normalizedError approximationError
    positivity
  · have hh := mul_le_mul_of_nonneg_left (normalizedError_schedule A P ht)
      (by positivity : 0≤(2*d+2:ℝ))
    have he : (2*d+2:ℝ)*tolerance s d=Real.exp (-8*s) := by
      unfold tolerance
      field_simp
    exact hh.trans_eq he

theorem filter_error_le_one {s : ℝ} (hs : 0≤s) (d : ℕ) :
    traceError A P (rawTolerance A P (tolerance s d)) (lowerHeight A P (tolerance s d))
      (newtonDepth A P (tolerance s d)) d≤1 :=
  (filter_error_bounds A P s d).2.trans (Real.exp_le_one_iff.mpr (by linarith))

/-- The sharp Fourier majorant grows only quartically at the chosen accuracy;
the exponentially large observation degree does not enter that majorant. -/
theorem majorant_growth {C : ℝ} (hC : 0≤C) : ∃K : ℝ,0≤K ∧ ∀s : ℝ,1≤s →
    ∀d : ℕ,(d:ℝ)≤Real.exp (C*s^2) →
      traceMajorant A P (newtonDepth A P (tolerance s d))≤K*s^4 := by
  obtain ⟨B,hB,hb⟩ := (newton_growth A P).1
  let D := 8+Real.log 4+C
  let c := ((Real.sqrt (gramLower A P))⁻¹)^2
  have hD : 0≤D := by
    have := Real.log_nonneg (by norm_num : (1:ℝ)≤4)
    dsimp only [D]
    linarith
  refine ⟨c+B*D^2,by dsimp only [c]; positivity,fun s hs d hd => ?_⟩
  have hu := logAccuracy_bounds hC hs d hd
  have hn := hb (logAccuracy s d) hu.1
  have hsq : (logAccuracy s d)^2≤D^2*s^4 := by
    have ht := mul_self_le_mul_self (zero_le_one.trans hu.1) hu.2
    nlinarith only [ht]
  have hp : ((3/2:ℝ)^newtonDepth A P (tolerance s d))^2≤(4:ℝ)^newtonDepth A P (tolerance s d) := by
    rw [←pow_mul,pow_mul']
    exact pow_le_pow_left₀ (by positivity) (by norm_num) _
  have hn' : (4:ℝ)^newtonDepth A P (tolerance s d)≤B*D^2*s^4 := by
    rw [tolerance_eq]
    exact hn.trans ((mul_le_mul_of_nonneg_left hsq hB).trans_eq (by ring))
  have hs4 : 1≤s^4 := one_le_pow₀ hs
  have hc : 0≤c := sq_nonneg _
  unfold traceMajorant
  apply max_le
  · have hm := mul_le_mul_of_nonneg_left hs4 hc
    nlinarith [mul_nonneg (mul_nonneg hB (sq_nonneg D)) (by positivity : 0≤s^4)]
  · exact (hp.trans hn').trans (by nlinarith [mul_nonneg hc (by positivity : 0≤s^4)])

/-- The actual Fourier trace approximation has the required exp(-3s) error.
The numerical trace-error side conditions follow from filter_error_bounds. -/
theorem approximation_rate {C M : ℝ} (hC : 0≤C) (hM : 0≤M) :
    ∃K : ℝ,0≤K ∧ ∀s : ℝ,1≤s → ∀d : ℕ,(d:ℝ)≤Real.exp (C*s^2) →
      (2+2*traceMajorant A P (newtonDepth A P (tolerance s d))*M)*
        Real.sqrt (traceError A P (rawTolerance A P (tolerance s d)) (lowerHeight A P (tolerance s d))
          (newtonDepth A P (tolerance s d)) d)≤K*Real.exp (-3*s) := by
  obtain ⟨B,hB,hb⟩ := majorant_growth A P hC
  refine ⟨24*(2+2*B*M),by positivity,fun s hs d hd => ?_⟩
  have he := (filter_error_bounds A P s d).2
  have hsqrt : Real.sqrt (traceError A P (rawTolerance A P (tolerance s d)) (lowerHeight A P (tolerance s d))
      (newtonDepth A P (tolerance s d)) d)≤Real.exp (-4*s) := by
    apply (Real.sqrt_le_sqrt he).trans_eq
    rw [show Real.exp (-8*s)=(Real.exp (-4*s))^2 by rw [←Real.exp_nat_mul]; congr 1; ring]
    exact Real.sqrt_sq (Real.exp_nonneg _)
  have hmajor := hb s hs d hd
  have hs4 : 1≤s^4 := one_le_pow₀ hs
  have hfront : 2+2*traceMajorant A P (newtonDepth A P (tolerance s d))*M≤(2+2*B*M)*s^4 := by
    have hm := mul_le_mul_of_nonneg_right hmajor hM
    nlinarith only [hm,hs4]
  have hq := QuantitativeHolomorphic.Schedule.quartic_exp_decay (zero_le_one.trans hs)
  calc
    _ ≤ ((2+2*B*M)*s^4)*Real.exp (-4*s) := mul_le_mul hfront hsqrt (Real.sqrt_nonneg _) (by positivity)
    _ = (2+2*B*M)*(s^4*Real.exp (-4*s)) := by ring
    _ ≤ (2+2*B*M)*(24*Real.exp (-3*s)) := mul_le_mul_of_nonneg_left hq (by positivity)
    _ = _ := by ring

theorem fixed_source_rate (s : ℝ) (d : ℕ) :
    ((2*d+2:ℝ)*tolerance s d/P.ε)/(4*Real.pi)=
      Real.exp (-8*s)/(4*Real.pi*P.ε) := by
  unfold tolerance
  have hd : (2*d+2:ℝ)≠0 := by positivity
  field_simp

#print axioms logAccuracy_growth
#print axioms fixed_source_rate
#print axioms tolerance_eq
#print axioms logAccuracy_bounds
#print axioms filter_error_bounds
#print axioms filter_error_le_one
#print axioms majorant_growth
#print axioms approximation_rate
end QuantitativeArithmeticRetainedApproximationSchedule
