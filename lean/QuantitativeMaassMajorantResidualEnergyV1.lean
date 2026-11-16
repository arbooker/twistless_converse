module

public import QuantitativeMaassWindowResidualShiftBoundV1
public import QuantitativeMaassColumnLinearEnergyV1
public import QuantitativeMaassMajorantTransferMassV1

set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled

/-- The actual original majorant's residual about the original center. -/
def originalMajorantResidualColumn (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (he : Function.Even K)
    (ε : ℝ→ℝ) (t : ℝ) : ℍ→Lp ℂ 2 (quotientMeasure 0) :=
  let f := QuantitativeNinaMaass.originalWindowMajorant K hc ε t
  cylinderTimeColumn (spectralResidualSchwartz t f)
    (spectralResidualSchwartz_compact t f (QuantitativeNinaMaass.originalWindowMajorant_compact K hc ε t))
    (spectralResidualSchwartz_even t f (QuantitativeNinaMaass.originalWindowMajorant_even K he hc ε t))
    (supportRadius K hc*radius ε t) (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le
    (spectralTimeResidual_support t f _ (originalMajorant_support K hc ε t))

/-- Splitting the enlarged interval into two short intervals and changing
the residual center proves the literal majorant residual energy bound. -/
theorem originalMajorant_residual_energy_schedule (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (o : ℍ) (H : ℝ) (hH : 0≤H) (ε : ℝ→ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∃ E : ℝ,0<E ∧ ∀ᶠ t in atTop,∀ L : ℝ,0≤L → L≤H*Strong.strongScale t →
      (∫ z in Metric.closedBall o L,‖originalMajorantResidualColumn K hc he ε t z‖^2)≤
        (t^3*ε t)*Real.exp (E*Strong.strongScale t) := by
  obtain ⟨A,B,hA,hB,hbound⟩ := windowResidualColumn_shifted_exponential_energy K he hc hK hm o
  obtain ⟨_,hresolve⟩ := propagation_limits slowScale ε
    (slowScale_tendsto.eventually (eventually_gt_atTop (0:ℝ)))
    (hε.mono (fun _ h => h.1)) hp
  refine ⟨A*(H+1)+1,by positivity,?_⟩
  filter_upwards [column_energy_cost_schedule A (16*B) H hA (by positivity) hH ε hε hp,
    hε,QuantitativeNinaMaass.originalWindowMajorant_parameters ε hε hp,
    radius_eventually_eq ε hε hp,hresolve.eventually (eventually_ge_atTop (2:ℝ)),
    eventually_ge_atTop (3:ℝ)] with t hcost heps hparam hrad hresolve ht
  intro L hL hLH
  have ht0 : 0≤t := by linarith
  have heps0 : 0≤ε t := heps.1.le
  let R := radius ε t
  have hR : 1≤R := le_max_left _ _
  have hRp : 0<R := radius_pos ε t
  let d := smoothingWidth (slowScale t) (ε t)
  let u := t-d
  let v := t+ε t+d
  let c := t+ε t/2
  let w := ε t/2+d
  have hd : 0≤d := hparam.1.le
  have hdε : 2*d≤ε t := hparam.2.1
  have hw : 0≤w := by dsimp [w]; linarith
  have hwε : w≤ε t := by dsimp [w]; linarith
  have hw1 : w≤1 := hwε.trans heps.2
  have huw : u+w=c := by dsimp [u,w,c]; ring
  have hcw : c+w=v := by dsimp [c,w,v]; ring
  have huc : u≤c := by linarith
  have hcv : c≤v := by linarith
  have hu : |u-t|≤1 := by rw [abs_le]; dsimp [u]; constructor <;> linarith [heps.2]
  have hc' : |c-t|≤1 := by rw [abs_le]; dsimp [c]; constructor <;> linarith [heps.2,heps.1]
  have hRw : 1/R≤w := by
    apply (div_le_iff₀ hRp).mpr
    have hr : 2≤R*ε t := by simpa only [R,hrad] using hresolve
    have hew : ε t/2≤w := by dsimp [w]; linarith
    nlinarith [mul_le_mul_of_nonneg_left hew hRp.le]
  let f₁ := windowTimeSchwartz K hc R hRp u c
  let f₂ := windowTimeSchwartz K hc R hRp c v
  let f := QuantitativeNinaMaass.originalWindowMajorant K hc ε t
  let α : ℂ := (QuantitativeNinaMaass.windowEnergyDenominator K ε t:ℂ)⁻¹
  have hsplit : f=α • f₁+α • f₂ := by
    change α • windowTimeSchwartz K hc R hRp u v=_
    rw [windowTimeSchwartz_add_intervals K hc R hRp u c v huc hcv,smul_add]
  let R₀ := supportRadius K hc*R
  have hR₀ : 0≤R₀ := (mul_pos (supportRadius_pos K hc) hRp).le
  have hc₁ := symmetricWindowTimeTest_compact K hc R u c hRp
  have hc₂ := symmetricWindowTimeTest_compact K hc R c v hRp
  have he₁ := symmetricWindowTimeTest_even K he R u c
  have he₂ := symmetricWindowTimeTest_even K he R c v
  have hs₁ := (symmetricWindowTimeTest_uniform_support K hc).choose_spec.2 R hRp u c
  have hs₂ := (symmetricWindowTimeTest_uniform_support K hc).choose_spec.2 R hRp c v
  let q₁ := cylinderTimeColumn (spectralResidualSchwartz t f₁)
    (spectralResidualSchwartz_compact t f₁ hc₁) (spectralResidualSchwartz_even t f₁ he₁)
    R₀ hR₀ (spectralTimeResidual_support t f₁ R₀ hs₁)
  let q₂ := cylinderTimeColumn (spectralResidualSchwartz t f₂)
    (spectralResidualSchwartz_compact t f₂ hc₂) (spectralResidualSchwartz_even t f₂ he₂)
    R₀ hR₀ (spectralTimeResidual_support t f₂ R₀ hs₂)
  have hb₁ : (∫ z in Metric.closedBall o L,‖q₁ z‖^2)≤B*(t^3*w)*Real.exp (A*(R+L)) := by
    have hh := hbound L R t u w hR hL ht hu hw hw1 hRw
    simp only [huw] at hh
    exact hh R₀ hR₀ hs₁
  have hb₂ : (∫ z in Metric.closedBall o L,‖q₂ z‖^2)≤B*(t^3*w)*Real.exp (A*(R+L)) := by
    have hh := hbound L R t c w hR hL ht hc' hw hw1 hRw
    simp only [hcw] at hh
    exact hh R₀ hR₀ hs₂
  have hlin := cylinderTimeColumn_linear_energy
    (spectralResidualSchwartz t f₁) (spectralResidualSchwartz t f₂) (spectralResidualSchwartz t f)
    (spectralResidualSchwartz_compact t f₁ hc₁) (spectralResidualSchwartz_compact t f₂ hc₂)
    (spectralResidualSchwartz_compact t f (QuantitativeNinaMaass.originalWindowMajorant_compact K hc ε t))
    (spectralResidualSchwartz_even t f₁ he₁) (spectralResidualSchwartz_even t f₂ he₂)
    (spectralResidualSchwartz_even t f (QuantitativeNinaMaass.originalWindowMajorant_even K he hc ε t))
    R₀ hR₀ (spectralTimeResidual_support t f₁ R₀ hs₁) (spectralTimeResidual_support t f₂ R₀ hs₂)
    (spectralTimeResidual_support t f R₀ (originalMajorant_support K hc ε t)) α α
    (by rw [hsplit,spectralResidualSchwartz_linear]) (Metric.closedBall o L) (isCompact_closedBall o L)
  have hα : ‖α‖^2≤4 := by
    have hd' := QuantitativeNinaMaass.windowEnergyDenominator_pos K ε t
    have hi := inv_anti₀ (by norm_num : (0:ℝ)<1/2)
      (le_max_left (1/2:ℝ) (1-(∫ x,|x| * K x)/(positiveWindowRadius ε t*d)))
    have hi' : (QuantitativeNinaMaass.windowEnergyDenominator K ε t)⁻¹≤2 := by
      simpa only [QuantitativeNinaMaass.windowEnergyDenominator,one_div,inv_inv,d] using hi
    dsimp only [α]
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd']
    nlinarith [inv_pos.mpr hd']
  calc
    _≤2*‖α‖^2*(∫ z in Metric.closedBall o L,‖q₁ z‖^2)+
        2*‖α‖^2*(∫ z in Metric.closedBall o L,‖q₂ z‖^2) := hlin
    _≤8*(B*(t^3*w)*Real.exp (A*(R+L)))+8*(B*(t^3*w)*Real.exp (A*(R+L))) := by
      apply add_le_add <;> apply mul_le_mul
      · nlinarith
      · exact hb₁
      · exact integral_nonneg (fun _ => sq_nonneg _)
      · norm_num
      · nlinarith
      · exact hb₂
      · exact integral_nonneg (fun _ => sq_nonneg _)
      · norm_num
    _≤8*(B*(t^3*ε t)*Real.exp (A*(R+L)))+8*(B*(t^3*ε t)*Real.exp (A*(R+L))) := by gcongr
    _=(t^3*ε t)*((16*B)*Real.exp (A*(R+L))) := by ring
    _≤_ := mul_le_mul_of_nonneg_left (hcost L hLH) (by positivity)

#print axioms originalMajorant_residual_energy_schedule
end QuantitativeMaass.Scheduled
