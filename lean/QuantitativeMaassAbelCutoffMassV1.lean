module

public import QuantitativeMaassAbelPositiveProfileV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

def abelCutoffTimeWeight (R t : ℝ) : ℝ :=
  abelCutoffReal (Real.cosh R-1) (Real.cosh t)*Real.cosh (t/2)

def abelCutoffMass (R : ℝ) : ℝ := ∫ t,abelCutoffTimeWeight R t

theorem abelCutoffTimeWeight_continuous (R : ℝ) : Continuous (abelCutoffTimeWeight R) :=
  ((abelCutoffReal_smooth _).continuous.comp Real.continuous_cosh).mul (by fun_prop)

theorem abelCutoffTimeWeight_integrable (R : ℝ) (hR : 0<R) :
    Integrable (abelCutoffTimeWeight R) := by
  have h := coshWeightedTest_integrable (abelCutoff (Real.cosh R-1)) (abelCutoff_smooth _)
    R hR.le (abelCutoff_radius_support R hR)
  have he (t : ℝ) : (Real.cosh (t/2):ℂ)*coshTimeTest (abelCutoff (Real.cosh R-1)) t=
      (abelCutoffTimeWeight R t:ℂ) := by
    simp only [coshTimeTest,abelCutoff,abelCutoffTimeWeight,Complex.ofReal_mul]
    ring
  have hi : Integrable (fun t => ((Real.cosh (t/2):ℂ)*coshTimeTest (abelCutoff (Real.cosh R-1)) t).re) := h.re
  simpa only [he,Complex.ofReal_re] using hi

/-- Strict positivity comes from the concrete time test's value at zero,
continuity and positivity of Lebesgue measure on open intervals. -/
theorem abelCutoffMass_pos (R : ℝ) (hR : 0<R) : 0<abelCutoffMass R := by
  apply integral_pos_of_integrable_nonneg_nonzero (abelCutoffTimeWeight_continuous R)
    (abelCutoffTimeWeight_integrable R hR)
    (fun t => mul_nonneg (abelCutoffReal_nonneg _ _) (Real.cosh_pos _).le) (x:=0)
  simp [abelCutoffTimeWeight,abelCutoffReal_one]

theorem abelCutoffProfile_mass (R : ℝ) (hR : 0<R) :
    (2*Real.pi:ℂ)*(∫ q in Ioi (1:ℝ),abelProfile (abelCutoff (Real.cosh R-1)) q)=
      (abelCutoffMass R:ℂ) := by
  have ha : 0<Real.cosh R-1 := sub_pos.mpr (Real.one_lt_cosh.mpr (ne_of_gt hR))
  rw [abelProfile_time_mass _ (abelCutoff_smooth _) (abelCutoff_compact _ ha)
    R hR.le (abelCutoff_radius_support R hR)]
  change (∫ t,coshTimeTest (abelCutoff (Real.cosh R-1)) t*(Real.cosh (t/2):ℂ))=
    ((∫ t,abelCutoffTimeWeight R t:ℝ):ℂ)
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with t
  simp only [coshTimeTest,abelCutoff,abelCutoffTimeWeight,Complex.ofReal_mul]

/-- Positivity identifies the absolute radial mass with its exact scalar mass. -/
theorem abelCutoffProfile_norm_mass (R : ℝ) (hR : 0<R) :
    2*Real.pi*(∫ q in Ioi (1:ℝ),‖abelProfile (abelCutoff (Real.cosh R-1)) q‖)=
      abelCutoffMass R := by
  have ha : 0<Real.cosh R-1 := sub_pos.mpr (Real.one_lt_cosh.mpr (ne_of_gt hR))
  have he : (∫ q in Ioi (1:ℝ),abelProfile (abelCutoff (Real.cosh R-1)) q)=
      ((∫ q in Ioi (1:ℝ),‖abelProfile (abelCutoff (Real.cosh R-1)) q‖:ℝ):ℂ) := by
    rw [← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro q hq
    dsimp only
    rw [abelCutoffProfile_norm _ ha q hq.le,abelCutoffProfile_eq]
  have hm := abelCutoffProfile_mass R hR
  rw [he] at hm
  exact_mod_cast hm

#print axioms abelCutoffMass_pos
#print axioms abelCutoffProfile_mass
#print axioms abelCutoffProfile_norm_mass

end QuantitativeMaass
