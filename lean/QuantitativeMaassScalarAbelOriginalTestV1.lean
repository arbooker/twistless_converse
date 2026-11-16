module

public import QuantitativeMaassScalarAbelCauchyV1
public import QuantitativeMaassScalarAbelBoundaryV1
public import QuantitativeMaassAbelOriginalTestRepresentationV1
public import QuantitativeMaassAbelZeroVelocityV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass

theorem scalarAbelDistribution_toSmooth (f : ℍ → ℂ) (hf : Continuous f) (x : ℍ)
    (ψ : PositiveTimeTest) :
    scalarAbelDistribution f hf x ψ.toSmooth=scalarPositiveAbel f x ψ :=
  scalarPositiveAbel_congr f x _ ψ (funext (fun t => ψ.toSmooth_coe t))

/-- A continuous positive-time representation extends to every original
real compact q-test, including tests nonzero at q=1. -/
theorem scalarAbel_originalTest (f : ℍ → ℂ) (hf : Continuous f) (x : ℍ)
    (v : ℝ → ℂ) (hv : Continuous v)
    (hvT : ∀ φ : PositiveSmoothTest,scalarAbelDistribution f hf x φ=∫ t,φ t • v t)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    scalarAbelConvolution f x F=∫ t in Ioi (0:ℝ),coshTimeTest F t*v t := by
  let a : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have ha (n : ℕ) : 0<a n := by dsimp [a]; positivity
  have ha1 (n : ℕ) : a n≤1 := by
    dsimp [a]
    exact (div_le_one (by positivity)).mpr (by have h := Nat.cast_nonneg (α:=ℝ) n; linarith)
  have ha0 : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let ψ (n : ℕ) := abelPuncturedPositiveTest F hF hr R hR hs (a n) (ha n) (ha1 n)
  have he (n : ℕ) : scalarPositiveAbel f x (ψ n)=
      ∫ t in Ioi (0:ℝ),coshTimeTest (fun q => F q-abelBoundaryPart F (a n) q) t • v t := by
    have h := hvT (ψ n).toSmooth
    rw [scalarAbelDistribution_toSmooth,PositiveTimeTest.toSmooth_integral (ψ n) v] at h
    rw [h]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change 0<t at ht
    change positiveCoshTest (fun q => F q-abelBoundaryPart F (a n) q) t • v t=_
    simp only [positiveCoshTest,ite_eq_left ht,coshTimeTest]
  have hb := scalarAbelBoundary_tendsto atTop f hf x F hF hc R hR hs a ha ha1 ha0
  have hg : Tendsto (fun n => scalarPositiveAbel f x (ψ n)) atTop
      (𝓝 (scalarAbelConvolution f x F)) := by
    have hh := (tendsto_const_nhds (x:=scalarAbelConvolution f x F)).sub hb
    simp only [sub_zero] at hh
    apply hh.congr'
    filter_upwards with n
    exact (scalarAbelPunctured_eq f hf x F hF hc hr R hR hs (a n) (ha n) (ha1 n)).symm
  have hi := coshPuncturedCurve_tendsto atTop F hF R hR hs v hv a ha ha0
  exact tendsto_nhds_unique hg (hi.congr' (Eventually.of_forall (fun n => (he n).symm)))

/-- The endpoint equation forces the initial velocity of the recovered
scalar Cauchy evolution to vanish. -/
theorem scalarAbel_zero_velocity (u : ℝ×ℝ → ℂ)
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2}) (e : ℂ)
    (he : ∀ y : ℍ,upperLaplacian u y=e*upperFunction u y) (x : ℍ) (c : ℂ × ℂ)
    (hcT : ∀ φ : PositiveSmoothTest,
      scalarAbelDistribution (upperFunction u) (upperFunction_continuous hu) x φ=
        ∫ t,φ t • boundedCauchyPosition ((scalarAbelGenerator e).restrictScalars ℝ) c t) :
    c.2=0 := by
  let F := abelCutoff (Real.cosh 1-1)
  have hF : ContDiff ℝ ∞ F := abelCutoff_smooth _
  have hc : HasCompactSupport F := abelCutoff_compact _ (sub_pos.mpr (Real.one_lt_cosh.mpr (by norm_num)))
  have hr : ∀ q,star (F q)=F q := by
    intro q
    simp only [F,abelCutoff,Complex.star_def,Complex.conj_ofReal]
  have hs : Function.support F⊆Iic (Real.cosh 1) := abelCutoff_radius_support 1 (by norm_num)
  let A := scalarAbelGenerator e
  let v := boundedCauchyPosition (A.restrictScalars ℝ) c
  have hv : Continuous v := boundedCauchyPosition_continuous _ c
  have hq := classical_abel_convolution_equation F hF hc hr 1 (by norm_num) hs u hu e he x
  change scalarAbelConvolution (upperFunction u) x (coshTimeOperator F)=
    (1/4-e)*scalarAbelConvolution (upperFunction u) x F at hq
  rw [scalarAbel_originalTest _ (upperFunction_continuous hu) x v hv hcT F hF hc hr 1 (by norm_num) hs,
    scalarAbel_originalTest _ (upperFunction_continuous hu) x v hv hcT (coshTimeOperator F)
      (coshTimeOperator_smooth F hF) (coshTimeOperator_compact F hc)
      (coshTimeOperator_real F hr) 1 (by norm_num) (coshTimeOperator_support F _ hs)] at hq
  have hb := boundedCauchy_cosh_boundary A c F hF 1 (by norm_num) hs
  change (∫ t in Ioi (0:ℝ),coshTimeTest (coshTimeOperator F) t*v t)+
    (e-1/4)*(∫ t in Ioi (0:ℝ),coshTimeTest F t*v t)=F 1*(-c.2) at hb
  rw [hq] at hb
  have hf1 : F 1=1 := by simp only [F,abelCutoff,abelCutoffReal_one,Complex.ofReal_one]
  rw [hf1,one_mul] at hb
  have hz : (1/4-e)*(∫ t in Ioi (0:ℝ),coshTimeTest F t*v t)+
      (e-1/4)*(∫ t in Ioi (0:ℝ),coshTimeTest F t*v t)=0 := by ring
  rw [hz] at hb
  exact neg_eq_zero.mp hb.symm

#print axioms scalarAbelDistribution_toSmooth
#print axioms scalarAbel_originalTest
#print axioms scalarAbel_zero_velocity

end QuantitativeMaass
