module
public import SmallLevelTaylorTermMellinV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticCurvedTaylor
open Complex Filter Set MeasureTheory Asymptotics SmallLevelTaylor
open FinitenessPolynomialSeries FinitenessFourierConstruction
open scoped Topology

theorem one_add_imaginary_ne_zero (t : ℝ) : (1:ℂ)+(t:ℂ)*I≠0 := by
  intro h
  have hh := congrArg Complex.re h
  norm_num at hh

theorem curved_point_height (β c r y : ℝ) :
    (deformPoint β c y (((y/r:ℝ):ℂ)*I)).im=(y/c)/(1+(y/r)^2) := by
  rw [deformPoint_im,Complex.inv_re]
  have hre : ((1:ℂ)+((y/r:ℝ):ℂ)*I).re=1 := by
    simp only [add_re,one_re,mul_I_re,ofReal_im,neg_zero,add_zero]
  have him : ((1:ℂ)+((y/r:ℝ):ℂ)*I).im=y/r := by
    simp only [add_im,one_im,mul_I_im,ofReal_re,zero_add]
  rw [Complex.normSq_apply,hre,him]
  ring

def curved (k : ℕ) (a : ℕ → ℂ) (β c r y : ℝ) : ℂ :=
  deformed k a β c y (((y/r:ℝ):ℂ)*I)

theorem curved_continuous (k : ℕ) {a : ℕ → ℂ} (ha : PolynomialBound a)
    (β r : ℝ) {c : ℝ} (hc : 0<c) : ContinuousOn (curved k a β c r) (Ioi 0) := by
  have hp : Continuous (fun y : ℝ => deformPoint β c y (((y/r:ℝ):ℂ)*I)) := by
    unfold deformPoint
    fun_prop (disch := intro y; exact one_add_imaginary_ne_zero (y/r))
  intro y hy
  have hypos : 0<(deformPoint β c y (((y/r:ℝ):ℂ)*I)).im := by
    rw [curved_point_height]
    exact div_pos (div_pos hy hc) (by positivity)
  have hf := (FinitenessFourierConstruction.holomorphic ha hypos).continuousAt.comp
    (f := fun y : ℝ => deformPoint β c y (((y/r:ℝ):ℂ)*I)) hp.continuousAt
  have hfac : Continuous (fun y : ℝ => (((1:ℂ)+((y/r:ℝ):ℂ)*I)^k)⁻¹) := by
    fun_prop (disch := intro y; exact pow_ne_zero k (one_add_imaginary_ne_zero (y/r)))
  exact (hfac.continuousAt.mul hf).continuousWithinAt

theorem locallyIntegrableOn_indicator {f : ℝ → ℂ} {s t : Set ℝ}
    (hf : LocallyIntegrableOn f s) (ht : MeasurableSet t) :
    LocallyIntegrableOn (t.indicator f) s := by
  intro x hx
  obtain ⟨u,hu,hfu⟩ := hf x hx
  exact ⟨u,hu,hfu.indicator ht⟩

def truncated (k : ℕ) (a : ℕ → ℂ) (β c r T : ℝ) : ℝ → ℂ :=
  (Iic T).indicator (curved k a β c r)

def polynomial (k : ℕ) (a : ℕ → ℂ) (β c r : ℝ) (M : ℕ) (y : ℝ) : ℂ :=
  ∑ n∈Finset.range M, taylorTerm k a β c r n y

def remainder (k : ℕ) (a : ℕ → ℂ) (β c r T : ℝ) (M : ℕ) (y : ℝ) : ℂ :=
  truncated k a β c r T y-polynomial k a β c r M y

theorem polynomial_continuous (k : ℕ) {a : ℕ → ℂ} (ha : PolynomialBound a)
    (β r : ℝ) {c : ℝ} (hc : 0<c) (M : ℕ) :
    ContinuousOn (polynomial k a β c r M) (Ioi 0) := by
  unfold polynomial
  apply continuousOn_finsetSum
  intro n hn
  exact cauchy_term_continuous k ha β r hc n

theorem remainder_locallyIntegrable (k : ℕ) {a : ℕ → ℂ} (ha : PolynomialBound a)
    (β r T : ℝ) {c : ℝ} (hc : 0<c) (M : ℕ) :
    LocallyIntegrableOn (remainder k a β c r T M) (Ioi 0) :=
  (locallyIntegrableOn_indicator ((curved_continuous k ha β r hc).locallyIntegrableOn
    measurableSet_Ioi) measurableSet_Iic).sub
      ((polynomial_continuous k ha β r hc M).locallyIntegrableOn measurableSet_Ioi)

theorem remainder_small (k : ℕ) {a : ℕ → ℂ} (ha : PolynomialBound a) (ha0 : a 0=0)
    {c : ℝ} (hc : 0<c) : ∃ K : ℕ, ∀ β r T : ℝ, r≠0 → 0<T → ∀ M : ℕ,
    remainder k a β c r T M=O[𝓝[>] 0] (fun y : ℝ => y^((M:ℝ)-(K:ℝ))) := by
  obtain ⟨K,hK⟩ := taylorRemainder_small ha ha0 k hc
  refine ⟨K,fun β r T hr hT M => ?_⟩
  have he : remainder k a β c r T M =ᶠ[𝓝[>] 0] taylorRemainder k a β c r M := by
    filter_upwards [(eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds] with y hy
    simp only [remainder,truncated,indicator_of_mem (show y∈Iic T from hy.le),
      curved,taylorRemainder,polynomial,FormalMultilinearSeries.partialSum,taylorTerm]
  exact (hK β r hr M).congr' he.symm Filter.EventuallyEq.rfl

theorem remainder_rapid (k : ℕ) {a : ℕ → ℂ} (ha : PolynomialBound a) (ha0 : a 0=0)
    (β r T : ℝ) {c : ℝ} (hc : 0<c) (M : ℕ) (s : ℝ) :
    remainder k a β c r T M=O[atTop] (fun y : ℝ => y^s) := by
  have hp : polynomial k a β c r M=O[atTop] (fun y : ℝ => y^s) := by
    unfold polynomial
    apply IsBigO.fun_sum
    intro n hn
    exact cauchy_term_rapid k ha ha0 β r hc n s
  have he : truncated k a β c r T =ᶠ[atTop] (fun _ => (0:ℂ)) := by
    filter_upwards [eventually_gt_atTop T] with y hy
    exact indicator_of_notMem (show y∉Iic T from not_le.mpr hy) _
  have hz : truncated k a β c r T=O[atTop] (fun y : ℝ => y^s) :=
    (isBigO_zero _ _).congr' he.symm Filter.EventuallyEq.rfl
  exact hz.sub hp

/-- A truncated curved ray has Taylor errors analytic on arbitrarily
large right half-planes. The truncation discontinuity is accounted for
through local integrability; no Fricke law for this new ray is assumed. -/
theorem remainder_mellin_analytic (k : ℕ) {a : ℕ → ℂ} (ha : PolynomialBound a)
    (ha0 : a 0=0) {c : ℝ} (hc : 0<c) :
    ∃ K : ℕ, ∀ β r T : ℝ, r≠0 → 0<T → ∀ M : ℕ,
      AnalyticOnNhd ℂ (mellin (remainder k a β c r T M)) {s : ℂ | (K:ℝ)-(M:ℝ)<s.re} := by
  obtain ⟨K,hK⟩ := remainder_small k ha ha0 hc
  refine ⟨K,fun β r T hr hT M => ?_⟩
  have hd : DifferentiableOn ℂ (mellin (remainder k a β c r T M))
      {s : ℂ | (K:ℝ)-(M:ℝ)<s.re} := by
    intro s hs
    exact (mellin_differentiableAt_of_isBigO_rpow
      (remainder_locallyIntegrable k ha β r T hc M)
      (remainder_rapid k ha ha0 β r T hc M (-(s.re+1))) (lt_add_one s.re)
      (by simpa only [neg_sub] using hK β r T hr hT M) hs).differentiableWithinAt
  exact hd.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

#print axioms remainder_mellin_analytic
end QuantitativeArithmeticCurvedTaylor
