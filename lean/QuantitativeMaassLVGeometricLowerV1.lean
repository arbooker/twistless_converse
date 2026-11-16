module

public import QuantitativeMaassMixedTraceLimitV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology SchwartzMap FourierTransform InnerProductSpace

namespace QuantitativeMaass

/-- The precise scalar polynomial of the actual LV operator. -/
def lvScalarSymbol (p d : ℕ) (z : ℝ × ℝ) : ℝ :=
  1-(1-(z.1-2*Real.cos (Real.log p*z.2))^2/(lvBound p)^2)^d

/-- Explicit inverse-square-root finite-place deficit, with actual normalization. -/
def lvSphericalDeficit (p d : ℕ) : ℝ :=
  unramifiedDensityBound (p:ℝ)*lvBound p*Real.sqrt Real.pi/Real.sqrt (d:ℝ)

/-- The finite-place integral of the actual scalar symbol is uniformly close
to one for all real spectral parameters, with a proved quantitative deficit. -/
theorem finitePlaceSymbol_actualLV_bounds (p : ℕ) [Fact p.Prime]
    (d : ℕ) (hd : 0<d) (r : ℝ) :
    1-lvSphericalDeficit p d≤finitePlaceSymbol p (lvScalarSymbol p d) r ∧
    finitePlaceSymbol p (lvScalarSymbol p d) r≤1 := by
  have hh := QuantitativeArithmeticTreePlancherel.tree_actual_lv_root_bounds p r d hd
  have hp := (Fact.out : p.Prime).one_lt
  rw [← QuantitativeArithmeticTreePlancherel.tree_polynomial_moments p hp] at hh
  have heq : QuantitativeArithmeticTreePlancherel.densityMoment p (by exact_mod_cast hp)
      (QuantitativeArithmeticTreePlancherel.treeLVPolynomial (2*Real.cos (r*Real.log p)) (lvBound p) d)=
      finitePlaceSymbol p (lvScalarSymbol p d) r := by
    simp only [QuantitativeArithmeticTreePlancherel.densityMoment,
      QuantitativeArithmeticTreePlancherel.treeLVPolynomial,LinearMap.coe_mk,AddHom.coe_mk,
      Polynomial.eval_sub,Polynomial.eval_one,Polynomial.eval_pow,Polynomial.eval_mul,
      Polynomial.eval_C,Polynomial.eval_X,finitePlaceSymbol,lvScalarSymbol]
    rw [intervalIntegral.integral_of_le (by norm_num : (-2:ℝ)≤2),← integral_Icc_eq_integral_Ioc]
    congr 1
    funext x
    rw [mul_comm r (Real.log p),div_eq_mul_inv,mul_comm ((lvBound p)^2)⁻¹]
  rw [heq] at hh
  exact hh

/-- The literal spherical main term of the actual LV filter retains at least
one minus its explicit deficit of the original positive window mass. -/
theorem windowSymbolIdentity_actualLV_bounds (N p : ℕ) [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (a₀ b₀ : ℤ) (hab₀ : (p:ℤ)*a₀+(N:ℤ)*b₀=1)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (R : ℝ) (hR : 0<R) (a b : ℝ) (ha : 0<a) (hab : a≤b) (d : ℕ) (hd : 0<d) :
    (1-lvSphericalDeficit p d)*(windowIdentityContribution K hc R hR a b).re≤
      windowSymbolIdentity p K R a b (lvScalarSymbol p d) ∧
    windowSymbolIdentity p K R a b (lvScalarSymbol p d)≤
      (windowIdentityContribution K hc R hR a b).re := by
  let w := fun r => (smoothedWindow K R (Icc a b∪Icc (-b) (-a)) r)^2*windowPlancherelWeight r
  have hw : Integrable w := (symmetric_squaredWindow_plancherel_mass a b ha hab K hK hm R hR).1
  have hw0 (r : ℝ) : 0≤w r := mul_nonneg (sq_nonneg _) (windowPlancherelWeight_nonneg r)
  have hI : Integrable (fun r => w r*finitePlaceSymbol p (lvScalarSymbol p d) r) :=
    mixedHeckeSpan_weight_integrable N p hN hpN a₀ b₀ hab₀ w hw
      (actualLVFilter_symbol_mem N p hN hpN a₀ b₀ hab₀ d)
  have hl := integral_mono (hw.const_mul (1-lvSphericalDeficit p d)) hI
    (fun r => by
      calc
        (1-lvSphericalDeficit p d)*w r = w r*(1-lvSphericalDeficit p d) := mul_comm _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (finitePlaceSymbol_actualLV_bounds p d hd r).1 (hw0 r))
  have hu := integral_mono hI hw (fun r => by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (finitePlaceSymbol_actualLV_bounds p d hd r).2 (hw0 r))
  rw [integral_const_mul] at hl
  have heq : (windowIdentityContribution K hc R hR a b).re=(1/(4*Real.pi))*(∫ r,w r) := by
    rw [windowIdentityContribution_eq_mass K he hc R hR a b ha]
    have hcast : (1/(4*Real.pi):ℂ)=((1/(4*Real.pi):ℝ):ℂ) := by push_cast;rfl
    rw [hcast,← Complex.ofReal_mul,Complex.ofReal_re]
  rw [heq]
  change (1-lvSphericalDeficit p d)*((1/(4*Real.pi))*(∫ r,w r))≤
      (1/(4*Real.pi))*(∫ r,w r*finitePlaceSymbol p (lvScalarSymbol p d) r) ∧ _
  constructor
  · calc
      _ = (1/(4*Real.pi))*((1-lvSphericalDeficit p d)*(∫ r,w r)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)
  · exact mul_le_mul_of_nonneg_left hu (by positivity)

/-- A genuine quantitative LV lower estimate for the actual full quotient
local trace, with degree fixed before the spectral limit. Parity and sharp
cuspidal counting are separate steps. -/
theorem actualLVFilter_window_eventual_lower (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (o : ℍ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (d : ℕ) (hd : 0<d) (η : ℝ) (hη : 0<η) :
    ∀ᶠ t in atTop,(1-lvSphericalDeficit p d)*(quotientMeasure N).real univ/(2*Real.pi)-η<
      windowLocalOperatorTrace N K he hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t)
        t (t+ε t) (Metric.closedBall o (positiveWindowRadius ε t))
        (actualLVFilter N p hN hpN a b hab d)/(t*ε t) := by
  have herror := actualLVFilter_window_trace_error N p hN hpN hNp a b hab K he hc hK hm o ε hε hproduct d
  have hi := (windowIdentityContribution_interval_normalized K he hc hK hm ε hε hproduct).const_mul
    ((quotientMeasure N).real univ*(1-lvSphericalDeficit p d))
  have hlim := herror.add hi
  simp only [zero_add] at hlim
  have hnear := hlim.eventually (lt_mem_nhds (by
    change (1-lvSphericalDeficit p d)*(quotientMeasure N).real univ/(2*Real.pi)-η<
      (quotientMeasure N).real univ*(1-lvSphericalDeficit p d)*(1/(2*Real.pi))
    rw [show (quotientMeasure N).real univ*(1-lvSphericalDeficit p d)*(1/(2*Real.pi))=
      (1-lvSphericalDeficit p d)*(quotientMeasure N).real univ/(2*Real.pi) by ring]
    exact sub_lt_self _ hη))
  filter_upwards [hnear,hε,eventually_gt_atTop (0:ℝ)] with t ht hεt htp
  apply lt_of_lt_of_le ht
  have hb := (windowSymbolIdentity_actualLV_bounds N p hN hpN a b hab K
    he hc hK hm _ (positiveWindowRadius_pos ε t)
    t (t+ε t) htp (le_add_of_nonneg_right hεt.1.le) d hd).1
  have hv : 0≤(quotientMeasure N).real univ := measureReal_nonneg
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb hv) (mul_pos htp hεt.1).le
  have numeric (X Y Z V D q : ℝ) (h : V*((1-D)*Z)/q≤V*Y/q) :
      (X-V*Y)/q+V*(1-D)*(Z/q)≤X/q := by
    ring_nf at h ⊢
    linarith only [h]
  exact numeric _ _ _ _ _ _ hh

#print axioms finitePlaceSymbol_actualLV_bounds
#print axioms windowSymbolIdentity_actualLV_bounds
#print axioms actualLVFilter_window_eventual_lower

end QuantitativeMaass
