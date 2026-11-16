module

public import QuantitativeMaassWindowColumnSplittingV1
public import QuantitativeArithmeticMaassColumnEnergyExponentialV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass

/-- A bounded shift of the window's left endpoint preserves the residual
energy estimate about the original center. -/
theorem windowResidualColumn_shifted_exponential_energy (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (o : ℍ) :
    ∃ A B : ℝ,0<A ∧ 0<B ∧ ∀ (L R t s ε : ℝ) (hR : 1≤R),
      0≤L → 3≤t → |s-t|≤1 → 0≤ε → ε≤1 → 1/R≤ε →
      let f := windowTimeSchwartz K hc R (lt_of_lt_of_le zero_lt_one hR) s (s+ε)
      ∀ Rout : ℝ,∀ hOut : 0≤Rout,∀ hs : Function.support f⊆Icc (-Rout) Rout,
      (∫ z in Metric.closedBall o L,
        ‖cylinderTimeColumn (spectralResidualSchwartz t f)
          (spectralResidualSchwartz_compact t f
            (symmetricWindowTimeTest_compact K hc R s (s+ε) (lt_of_lt_of_le zero_lt_one hR)))
          (spectralResidualSchwartz_even t f (symmetricWindowTimeTest_even K he R s (s+ε)))
          Rout hOut (spectralTimeResidual_support t f Rout hs) z‖^2)≤
        B*(t^3*ε)*Real.exp (A*(R+L)) := by
  obtain ⟨A₁,B₁,hA₁,hB₁,hsrc⟩ := windowSourceColumn_exponential_energy K he hc hK hm o
  obtain ⟨A₂,B₂,hA₂,hB₂,hres⟩ := windowResidualColumn_exponential_energy K he hc hK hm o
  refine ⟨A₁+A₂,16*B₂+36*B₁,by positivity,by positivity,?_⟩
  intro L R t s ε hR hL ht hst he0 he1 hresolve f Rout hOut hs
  have hst' := abs_le.mp hst
  have hs1 : 1≤s := by linarith
  have ht0 : 0≤t := by linarith
  have hs0 : 0≤s := by linarith
  have hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  let fc := symmetricWindowTimeTest_compact K hc R s (s+ε) hRp
  let fe := symmetricWindowTimeTest_even K he R s (s+ε)
  let c := cylinderTimeColumn f fc fe Rout hOut hs
  let r := cylinderTimeColumn (spectralResidualSchwartz s f)
    (spectralResidualSchwartz_compact s f fc) (spectralResidualSchwartz_even s f fe)
    Rout hOut (spectralTimeResidual_support s f Rout hs)
  let q := cylinderTimeColumn (spectralResidualSchwartz t f)
    (spectralResidualSchwartz_compact t f fc) (spectralResidualSchwartz_even t f fe)
    Rout hOut (spectralTimeResidual_support t f Rout hs)
  have hci : IntegrableOn (fun z => ‖c z‖^2) (Metric.closedBall o L) := by
    have hh : Continuous c := cylinderAbelColumn_continuous _ _ _ _ _
    exact (hh.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall o L)
  have hri : IntegrableOn (fun z => ‖r z‖^2) (Metric.closedBall o L) := by
    have hh : Continuous r := cylinderAbelColumn_continuous _ _ _ _ _
    exact (hh.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall o L)
  have hqi : IntegrableOn (fun z => ‖q z‖^2) (Metric.closedBall o L) := by
    have hh : Continuous q := cylinderAbelColumn_continuous _ _ _ _ _
    exact (hh.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall o L)
  have hcoeff : ‖(s:ℂ)^2-(t:ℂ)^2‖≤3*t := by
    rw [←Complex.ofReal_pow,←Complex.ofReal_pow,←Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs]
    calc
      _=|s-t| * |s+t| := by rw [←abs_mul]; congr 1; ring
      _≤1*(3*t) := mul_le_mul hst (by rw [abs_of_nonneg (by positivity)]; linarith)
        (abs_nonneg _) (by norm_num)
      _=_ := one_mul _
  have hpoint (z : ℍ) : ‖q z‖^2≤2*‖r z‖^2+18*t^2*‖c z‖^2 := by
    have heq : q z=r z+((s:ℂ)^2-(t:ℂ)^2) • c z :=
      cylinderTimeColumn_change_center t s f fc fe Rout hOut hs z
    have hn := norm_add_le (r z) (((s:ℂ)^2-(t:ℂ)^2) • c z)
    rw [←heq,norm_smul] at hn
    have hx := mul_le_mul_of_nonneg_right hcoeff (norm_nonneg (c z))
    have hh : ‖q z‖≤‖r z‖+3*t*‖c z‖ := by linarith
    have hh2 := pow_le_pow_left₀ (norm_nonneg _) hh 2
    nlinarith [sq_nonneg (‖r z‖-3*t*‖c z‖)]
  have hbound := integral_mono_ae hqi ((hri.const_mul 2).add (hci.const_mul (18*t^2)))
    (Eventually.of_forall hpoint)
  simp only [Pi.add_apply] at hbound
  rw [integral_add (hri.const_mul 2) (hci.const_mul (18*t^2)),integral_const_mul,
    integral_const_mul] at hbound
  have hsrc' := hsrc L R s ε hR hL hs1 he0 he1 hresolve Rout hOut hs
  have hres' := hres L R s ε hR hL hs1 he0 he1 Rout hOut hs
  have hsmall₁ : Real.exp (A₁*(R+L))≤Real.exp ((A₁+A₂)*(R+L)) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hA₂.le (show 0≤R+L by linarith)])
  have hsmall₂ : Real.exp (A₂*(R+L))≤Real.exp ((A₁+A₂)*(R+L)) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hA₁.le (show 0≤R+L by linarith)])
  have hs2 : s≤2*t := by linarith
  have hs3 : s^3≤8*t^3 := by
    have hh := pow_le_pow_left₀ hs0 hs2 3
    nlinarith only [hh]
  calc
    _≤2*(∫ z in Metric.closedBall o L,‖r z‖^2)+
        18*t^2*(∫ z in Metric.closedBall o L,‖c z‖^2) := hbound
    _≤2*(B₂*(s^3*ε)*Real.exp (A₂*(R+L)))+
        18*t^2*(B₁*(s*ε)*Real.exp (A₁*(R+L))) := by gcongr
    _≤2*(B₂*((8*t^3)*ε)*Real.exp ((A₁+A₂)*(R+L)))+
        18*t^2*(B₁*((2*t)*ε)*Real.exp ((A₁+A₂)*(R+L))) := by gcongr
    _=_ := by ring

#print axioms windowResidualColumn_shifted_exponential_energy
end QuantitativeMaass
