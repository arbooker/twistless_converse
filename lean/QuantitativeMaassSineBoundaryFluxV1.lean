module

public import QuantitativeMaassWaveSinePrimitiveV1
public import QuantitativeMaassAbelIntertwiningV1
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Twice integrating by parts on positive time retains both endpoint terms.
Only the test is compactly supported; the evolving vector need not decay. -/
theorem compactTest_second_boundary {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] [CompleteSpace H]
    (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (u u' u'' : ℝ → H) (hu : ∀ t,HasDerivAt u (u' t) t)
    (hu' : ∀ t,HasDerivAt u' (u'' t) t) (hu'' : Continuous u'') :
    (∫ t in Ioi (0:ℝ),deriv (deriv φ) t • u t-φ t • u'' t)=
      φ 0 • u' 0-deriv φ 0 • u 0 := by
  let flux : ℝ → H := fun t => deriv φ t • u t-φ t • u' t
  have hφ' := (contDiff_infty_iff_deriv.mp hφ).2
  have hφ'' := (contDiff_infty_iff_deriv.mp hφ').2
  have hd (t : ℝ) : HasDerivAt flux
      (deriv (deriv φ) t • u t-φ t • u'' t) t := by
    have h := (((hφ'.differentiable (by simp) t).hasDerivAt).smul (hu t)).sub
      (((hφ.differentiable (by simp) t).hasDerivAt).smul (hu' t))
    convert h using 1
    abel
  have huc : Continuous u := continuous_iff_continuousAt.mpr (fun t => (hu t).continuousAt)
  have hdc : Continuous (fun t => deriv (deriv φ) t • u t-φ t • u'' t) :=
    (hφ''.continuous.smul huc).sub (hφ.continuous.smul hu'')
  have hdcomp : HasCompactSupport (fun t => deriv (deriv φ) t • u t-φ t • u'' t) :=
    hc.deriv.deriv.smul_right.sub hc.smul_right
  have hfc : HasCompactSupport flux := hc.deriv.smul_right.sub hc.smul_right
  have ht : Tendsto flux atTop (𝓝 0) := by
    rw [hasCompactSupport_iff_eventuallyEq,Filter.coclosedCompact_eq_cocompact] at hfc
    exact (hfc.filter_mono atTop_le_cocompact).tendsto
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto' (fun t (_ : t∈Ici (0:ℝ)) => hd t)
    (hdc.integrable_of_hasCompactSupport hdcomp).integrableOn ht
  simpa only [flux,zero_sub,neg_sub] using hi

namespace Wave

open QuantitativeArithmeticMaassWave

/-- The sine family has a nonzero boundary defect: the ordinary time-test
PDE on the half-line contributes exactly the test value at zero times the
initial vector. This is the term that must be excluded in Abel uniqueness. -/
theorem quotientSine_test_boundary (N : ℕ) {v w : AutomorphicSpace N}
    (hvw : FriedrichsGraph N v w) (φ : ℝ → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ t in Ioi (0:ℝ),deriv (deriv φ) t • quotientSine N t v-
      φ t • ((1/4:ℂ) • quotientSine N t v-quotientSine N t w))=φ 0 • v := by
  have hu' (t : ℝ) : HasDerivAt (fun t => shiftedQuotientWave N t v)
      ((1/4:ℂ) • quotientSine N t v-quotientSine N t w) t := by
    simpa only [quotientWaveVelocity_eq_sine] using quotientWave_hasDerivAt N hvw t
  have hs (a : AutomorphicSpace N) : Continuous (fun t => quotientSine N t a) :=
    continuous_iff_continuousAt.mpr (fun t => (quotientSine_hasDerivAt N a t).continuousAt)
  have h := compactTest_second_boundary φ hφ hc
    (fun t => quotientSine N t v) (fun t => shiftedQuotientWave N t v)
    (fun t => (1/4:ℂ) • quotientSine N t v-quotientSine N t w)
    (quotientSine_hasDerivAt N v) hu' ((hs v).const_smul (1/4:ℂ) |>.sub (hs w))
  simpa only [quotientSine_zero,shiftedQuotientWave_zero,ContinuousLinearMap.id_apply,
    smul_zero,sub_zero] using h

/-- The defect for a literal smooth q-test is F(1), so it is detected by
allowed test functions in the original Abel operator equation. -/
theorem quotientSine_coshTest_boundary (N : ℕ) {v w : AutomorphicSpace N}
    (hvw : FriedrichsGraph N v w) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) :
    (∫ t in Ioi (0:ℝ),coshTimeOperator F (Real.cosh t) • quotientSine N t v-
      coshTimeTest F t • ((1/4:ℂ) • quotientSine N t v-quotientSine N t w))=F 1 • v := by
  have hc : HasCompactSupport (coshTimeTest F) :=
    (isCompact_Icc : IsCompact (Icc (-R) R)).of_isClosed_subset isClosed_closure
      (closure_minimal (coshTimeTest_support F R hR hs) isClosed_Icc)
  have h := quotientSine_test_boundary N hvw (coshTimeTest F)
    (hF.comp Real.contDiff_cosh) hc
  simpa only [coshTimeTest_second F hF,coshTimeTest,Real.cosh_zero] using h

#print axioms quotientSine_test_boundary
#print axioms quotientSine_coshTest_boundary

end Wave
end QuantitativeMaass
