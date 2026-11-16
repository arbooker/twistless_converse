module

public import QuantitativeMaassPositiveTestConversionV1
public import QuantitativeMaassCoshCurveLimitV1
public import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass

/-- Conversion to real LF tests preserves the actual vector integral. -/
theorem PositiveTimeTest.toSmooth_integral {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] (ψ : PositiveTimeTest) (u : ℝ → H) :
    (∫ t,ψ.toSmooth t • u t)=∫ t in Ioi (0:ℝ),ψ.toFun t • u t := by
  simp_rw [ψ.toSmooth_smul]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  have hz : ψ.toFun t=0 := by
    by_contra hn
    exact ht (ψ.left_pos.trans_le (ψ.support hn).1)
  rw [hz,zero_smul]

/-- Any continuous representation of the actual regularized positive-test
map extends to every original real smooth compact q-test. Both limits are
proved: geometric convergence in operator norm and vector dominated convergence. -/
theorem regularizedAbelDistribution_originalTest (N : ℕ) [NeZero N]
    (ε : ℝ) (f : AutomorphicSpace N) (u : ℝ → AutomorphicSpace N) (hu : Continuous u)
    (huT : ∀ φ : PositiveSmoothTest,regularizedAbelDistribution N ε f φ=∫ t,φ t • u t)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    Wave.resolventCutoffOperator (friedrichsResolvent N) ε (abelKernelOperator N F hF hc R hR hs f)=
      ∫ t in Ioi (0:ℝ),coshTimeTest F t • u t := by
  let a : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have ha (n : ℕ) : 0<a n := by dsimp [a]; positivity
  have ha1 (n : ℕ) : a n≤1 := by
    dsimp [a]
    exact (div_le_one (by positivity)).mpr (by have h := Nat.cast_nonneg (α:=ℝ) n; linarith)
  have ha0 : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let ψ (n : ℕ) := abelPuncturedPositiveTest F hF hr R hR hs (a n) (ha n) (ha1 n)
  let P := Wave.resolventCutoffOperator (friedrichsResolvent N) ε
  have he (n : ℕ) : P (positiveTimeAbelOperator N (ψ n) f)=
      ∫ t in Ioi (0:ℝ),coshTimeTest (fun q => F q-abelBoundaryPart F (a n) q) t • u t := by
    have h := huT (ψ n).toSmooth
    change P (abelTestDistribution N (ψ n).toSmooth f)=_ at h
    rw [PositiveTimeTest.toSmooth_operator N (ψ n),PositiveTimeTest.toSmooth_integral (ψ n) u] at h
    rw [h]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change 0<t at ht
    change positiveCoshTest (fun q => F q-abelBoundaryPart F (a n) q) t • u t=_
    simp only [positiveCoshTest,ite_eq_left ht,coshTimeTest]
  have hg := abelPuncturedPositiveTest_tendsto atTop N F hF hc hr R hR hs a ha ha1 ha0
  have hv : Tendsto (fun n => P (positiveTimeAbelOperator N (ψ n) f)) atTop
      (𝓝 (P (abelKernelOperator N F hF hc R hR hs f))) :=
    P.continuous.tendsto _ |>.comp
      ((ContinuousLinearMap.apply ℂ (AutomorphicSpace N) f).continuous.tendsto _ |>.comp hg)
  have hi := coshPuncturedCurve_tendsto atTop F hF R hR hs u hu a ha ha0
  exact tendsto_nhds_unique hv (hi.congr' (Eventually.of_forall (fun n => (he n).symm)))

/-- The recovered actual bounded Cauchy evolution represents the original
q-tests, including those that do not vanish at q=1. -/
theorem regularizedAbelPosition_originalTest (N : ℕ) [NeZero N]
    (ε : ℝ) (f : AutomorphicSpace N) (c : AutomorphicSpace N×AutomorphicSpace N)
    (hcT : ∀ φ : PositiveSmoothTest,regularizedAbelDistribution N ε f φ=
      ∫ t,φ t • boundedCauchyPosition (regularizedShiftedGenerator N ε) c t)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    Wave.resolventCutoffOperator (friedrichsResolvent N) ε (abelKernelOperator N F hF hc R hR hs f)=
      ∫ t in Ioi (0:ℝ),coshTimeTest F t • boundedCauchyPosition (regularizedShiftedGenerator N ε) c t :=
  regularizedAbelDistribution_originalTest N ε f _ (boundedCauchyPosition_continuous _ c)
    hcT F hF hc hr R hR hs

#print axioms PositiveTimeTest.toSmooth_integral
#print axioms regularizedAbelDistribution_originalTest
#print axioms regularizedAbelPosition_originalTest

end QuantitativeMaass
