module

public import QuantitativeArithmeticMaassCylinderRectangleMassV1
public import QuantitativeArithmeticMaassScheduledColumnEnergyV1
public import QuantitativeMaassCompactHeightScheduleV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled

/-- Only the off-diagonal mean term incurs the upper-height loss. -/
theorem rectangle_mean_cost (a b C U R t e s H : ℝ)
    (ha : 0<a) (_hb : 0≤b) (hC : 0≤C) (hU : 0≤U) (hR : 0≤R)
    (he : 0≤e) (he1 : e≤1) (hsize : b≤Real.exp (H*s)) :
    2*b*((C*Real.sqrt t*R^2*e^2)*
      (Real.pi*(2*(2*(|Real.cosh (2*(U*R))|+1)+1)+2)))*a⁻¹≤
      (24*Real.pi*C*a⁻¹)*Real.sqrt t*Real.exp ((2*U+2)*R+H*s) := by
  have hx : 0≤2*(U*R) := by positivity
  have hc : Real.cosh (2*(U*R))≤Real.exp (2*(U*R)) := by
    rw [Real.cosh_eq]
    have hh := Real.exp_le_exp.mpr (show -(2*(U*R))≤2*(U*R) by linarith)
    linarith
  have hcosh : |Real.cosh (2*(U*R))|=Real.cosh (2*(U*R)) :=
    abs_of_nonneg (Real.cosh_pos _).le
  have hfac : Real.pi*(2*(2*(|Real.cosh (2*(U*R))|+1)+1)+2)≤
      12*Real.pi*Real.exp (2*(U*R)) := by
    rw [hcosh]
    have h1 := Real.one_le_exp hx
    nlinarith [Real.pi_pos]
  have hr : R^2≤Real.exp (2*R) := by
    have hh : R≤Real.exp R := by linarith [Real.add_one_le_exp R]
    calc
      R^2≤(Real.exp R)^2 := pow_le_pow_left₀ hR hh 2
      _=_ := by rw [two_mul,Real.exp_add,pow_two]
  have he2 : e^2≤1 := by nlinarith
  calc
    _≤2*Real.exp (H*s)*((C*Real.sqrt t*Real.exp (2*R)*1)*
        (12*Real.pi*Real.exp (2*(U*R))))*a⁻¹ := by
      gcongr
    _=_ := by
      rw [Real.exp_add,show (2*U+2)*R=2*(U*R)+2*R by ring,Real.exp_add]
      ring

/-- Actual cylinder source mass on every rectangle up to exp(H*strongScale)
is O(t epsilon), without an exponential strong-scale factor on its diagonal
term. The constant is chosen before the width function. -/
theorem sharp_rectangle_source_mass_uniform (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (H : ℝ) :
    ∃ B : ℝ,0<B ∧ ∀ ε : ℝ→ℝ,
      (∀ᶠ t in atTop,0<ε t ∧ ε t≤1) →
      Tendsto (fun t => ε t*slowScale t) atTop atTop →
      ∀ᶠ t in atTop,∀ a b : ℝ,0<a → 0≤b → b≤Real.exp (H*Strong.strongScale t) →
        (∫ z in upperRectangle 0 1 a b,‖column K hc he ε t z‖^2)≤a⁻¹*B*(t*ε t) := by
  obtain ⟨C,hC,hdecay⟩ := oneSidedWindowSquare_abel_decay K he hc
  obtain ⟨D,hD,hdiag⟩ := windowIdentityContribution_resolved_bound K he hc hK hm
  let U := supportRadius K hc
  have hU : 0<U := supportRadius_pos K hc
  let E := 24*Real.pi*C
  refine ⟨2*D+1,by positivity,?_⟩
  intro ε hε hproduct
  have hcost := Strong.compact_height_geometric_cost ε (2*U+2) H E
    (hε.mono (fun _ h => h.1)) hproduct
  filter_upwards [radius_resolves_window ε hε hproduct,radius_eventually_eq ε hε hproduct,
    hcost.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),hε,
    eventually_ge_atTop (1:ℝ)] with t hresolve hrad hsmall heps ht
  intro a b ha hb hsize
  have ht0 : 0<t := lt_of_lt_of_le zero_lt_one ht
  have hR : 1≤radius ε t := le_max_left _ _
  have hsource := cylinderTimeColumn_rectangle_sharp_energy
    (time K hc ε t) (time_compact K hc ε t) (time_even K hc he ε t)
    (time_real K hc he ε t) (U*radius ε t) (mul_pos hU (radius_pos ε t)).le
    (time_support K hc ε t) a b ha hb
    (C*Real.sqrt t*(radius ε t)^2*(ε t)^2) (by positivity)
    (fun d hd => hdecay (radius ε t) (ε t) t d hR heps.1.le heps.2 ht hd)
  have hdiagonal : ‖abelProfile (evenCoshLift (timeConvolution (time K hc ε t)
      (time K hc ε t))) 1‖≤D*t*ε t :=
    hdiag (radius ε t) t (ε t) hR ht heps.1.le heps.2 hresolve.2
  have hmean := rectangle_mean_cost 1 b C U (radius ε t) t (ε t)
    (Strong.strongScale t) H (by norm_num) hb hC.le hU.le (radius_pos ε t).le heps.1.le heps.2 hsize
  have hsmall' : E*Real.sqrt t*Real.exp ((2*U+2)*radius ε t+H*Strong.strongScale t)≤t*ε t := by
    rw [Strong.log_compactCuspHeight,←hrad] at hsmall
    exact ((div_lt_one (mul_pos ht0 heps.1)).mp hsmall).le
  have hdiag' := mul_le_mul_of_nonneg_left hdiagonal (show 0≤2*a⁻¹ by positivity)
  change (∫ z in upperRectangle 0 1 a b,‖column K hc he ε t z‖^2)≤_ at hsource
  dsimp only [E] at hsmall'
  norm_num only [inv_one,mul_one] at hmean
  have hm := mul_le_mul_of_nonneg_right (hmean.trans hsmall') (inv_nonneg.mpr ha.le)
  nlinarith only [hsource,hm,hdiag']

#print axioms rectangle_mean_cost
/-- Fixed positive lower cutoff version. -/
theorem sharp_rectangle_source_mass (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (a H : ℝ) (ha : 0<a) :
    ∃ B : ℝ,0<B ∧ ∀ ε : ℝ→ℝ,
      (∀ᶠ t in atTop,0<ε t ∧ ε t≤1) →
      Tendsto (fun t => ε t*slowScale t) atTop atTop →
      ∀ᶠ t in atTop,∀ b : ℝ,0≤b → b≤Real.exp (H*Strong.strongScale t) →
        (∫ z in upperRectangle 0 1 a b,‖column K hc he ε t z‖^2)≤B*(t*ε t) := by
  obtain ⟨B,hB,hbound⟩ := sharp_rectangle_source_mass_uniform K hc he hK hm H
  refine ⟨a⁻¹*B,by positivity,?_⟩
  intro ε hε hp
  exact (hbound ε hε hp).mono (fun t ht b hb hs => ht a b ha hb hs)

#print axioms sharp_rectangle_source_mass_uniform
#print axioms sharp_rectangle_source_mass
end QuantitativeMaass.Scheduled
