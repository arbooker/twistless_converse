module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace QuantitativeMaass.IntegralSchur
variable {A : Type*} [MeasurableSpace A] {μ : Measure A}

/-- The weighted Cauchy--Schwarz row estimate, with integrability of the
actual complex product proved from the two finite moments. -/
theorem row_bound (k f : A → ℂ) (hk : Measurable k) (hf : Measurable f)
    (hi : Integrable k μ) (he : Integrable (fun y => ‖k y‖*‖f y‖^2) μ) :
    Integrable (fun y => k y*f y) μ ∧
    ‖∫ y,k y*f y ∂μ‖^2≤(∫ y,‖k y‖ ∂μ)*(∫ y,‖k y‖*‖f y‖^2 ∂μ) := by
  let u : A → ℝ := fun y => Real.sqrt ‖k y‖
  let v : A → ℝ := fun y => Real.sqrt ‖k y‖*‖f y‖
  have huM : Measurable u := hk.norm.sqrt
  have hvM : Measurable v := huM.mul hf.norm
  have hu2 (y : A) : u y^2=‖k y‖ := Real.sq_sqrt (norm_nonneg _)
  have hv2 (y : A) : v y^2=‖k y‖*‖f y‖^2 := by
    dsimp [v]
    rw [mul_pow,Real.sq_sqrt (norm_nonneg _)]
  have huv (y : A) : u y*v y=‖k y‖*‖f y‖ := by
    dsimp [u,v]
    rw [← mul_assoc,← pow_two,Real.sq_sqrt (norm_nonneg _)]
  have hu : MemLp u 2 μ := (memLp_two_iff_integrable_sq huM.aestronglyMeasurable).mpr
    (by simp_rw [hu2]; exact hi.norm)
  have hv : MemLp v 2 μ := (memLp_two_iff_integrable_sq hvM.aestronglyMeasurable).mpr
    (by simp_rw [hv2]; exact he)
  have hp : Integrable (fun y => ‖k y‖*‖f y‖) μ := by
    have hh : Integrable (fun y => u y*v y) μ := hu.integrable_mul hv
    simpa only [huv] using hh
  have hprod : Integrable (fun y => k y*f y) μ := by
    apply hp.mono' (hk.mul hf).aestronglyMeasurable
    filter_upwards with y
    exact le_of_eq (norm_mul _ _)
  have hc := integral_mul_norm_le_Lp_mul_Lq
    (p:=2) (q:=2) (Real.holderConjugate_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by simpa using hu) (by simpa using hv)
  have hun (y : A) : ‖u y‖=u y := Real.norm_of_nonneg (Real.sqrt_nonneg _)
  have hvn (y : A) : ‖v y‖=v y := Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  simp only [hun,hvn,Real.rpow_two,huv,hu2,hv2,← Real.sqrt_eq_rpow] at hc
  have ha : 0≤∫ y,‖k y‖ ∂μ := integral_nonneg (fun _ => norm_nonneg _)
  have hb : 0≤∫ y,‖k y‖*‖f y‖^2 ∂μ := integral_nonneg (fun _ => by positivity)
  refine ⟨hprod,?_⟩
  calc
    ‖∫ y,k y*f y ∂μ‖^2 ≤ (∫ y,‖k y‖*‖f y‖ ∂μ)^2 := by
      apply pow_le_pow_left₀ (norm_nonneg _) _
      simpa only [norm_mul] using norm_integral_le_integral_norm (fun y => k y*f y)
    _ ≤ (Real.sqrt (∫ y,‖k y‖ ∂μ)*Real.sqrt (∫ y,‖k y‖*‖f y‖^2 ∂μ))^2 :=
      pow_le_pow_left₀ (integral_nonneg (fun _ => by positivity)) hc 2
    _ = _ := by rw [mul_pow,Real.sq_sqrt ha,Real.sq_sqrt hb]

#print axioms row_bound
end QuantitativeMaass.IntegralSchur
