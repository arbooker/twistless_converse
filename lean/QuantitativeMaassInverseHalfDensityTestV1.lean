module

public import QuantitativeMaassHalfDensityTestV1
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Inverse half-density transform, extended by zero to nonpositive heights. -/
def inverseHalfDensityTest (ψ : ℝ → ℂ) (y : ℝ) : ℂ :=
  if 0<y then (Real.exp (Real.log y/2):ℂ)*ψ (Real.log y) else 0

theorem inverseHalfDensityTest_exp (ψ : ℝ → ℂ) (x : ℝ) :
    inverseHalfDensityTest ψ (Real.exp x)=(Real.exp (x/2):ℂ)*ψ x := by
  simp only [inverseHalfDensityTest,Real.exp_pos,ite_true,Real.log_exp]

theorem logHalfDensity_inverse (ψ : ℝ → ℂ) :
    logHalfDensity (inverseHalfDensityTest ψ)=ψ := by
  funext x
  rw [logHalfDensity,inverseHalfDensityTest_exp,← mul_assoc,← Complex.ofReal_mul,← Real.exp_add]
  have he : -x/2+x/2=0 := by ring
  rw [he,Real.exp_zero,Complex.ofReal_one,one_mul]

/-- A lower support bound removes the apparent singularity at height zero. -/
theorem inverseHalfDensityTest_zero_below (ψ : ℝ → ℂ) (A B : ℝ)
    (hs : Function.support ψ⊆Icc A B) (y : ℝ) (hy : y<Real.exp A) :
    inverseHalfDensityTest ψ y=0 := by
  unfold inverseHalfDensityTest
  split_ifs with hp
  · have hz : ψ (Real.log y)=0 := by
      by_contra hn
      have hm := hs hn
      have hl := (Real.log_lt_iff_lt_exp hp).mpr hy
      linarith [hm.1]
    rw [hz,mul_zero]
  · rfl

theorem inverseHalfDensityTest_support (ψ : ℝ → ℂ) (A B : ℝ)
    (hs : Function.support ψ⊆Icc A B) :
    Function.support (inverseHalfDensityTest ψ)⊆Icc (Real.exp A) (Real.exp B) := by
  intro y hy
  have hp : 0<y := by
    by_contra hn
    exact hy (by simp only [inverseHalfDensityTest,ite_eq_right hn])
  have hn : ψ (Real.log y)≠0 := by
    intro hz
    apply hy
    simp only [inverseHalfDensityTest,ite_eq_left hp,hz,mul_zero]
  have hm := hs hn
  constructor
  · simpa only [Real.exp_log hp] using Real.exp_le_exp.mpr hm.1
  · simpa only [Real.exp_log hp] using Real.exp_le_exp.mpr hm.2

/-- The inverse of every smooth supported log test is globally smooth;
below its positive support it is identically zero on an open neighborhood. -/
theorem inverseHalfDensityTest_smooth (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (A B : ℝ) (hs : Function.support ψ⊆Icc A B) :
    ContDiff ℝ ∞ (inverseHalfDensityTest ψ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hp : 0<y
  · have hl : ContDiffAt ℝ ∞ Real.log y := Real.contDiffAt_log.mpr hp.ne'
    have he : ContDiffAt ℝ ∞ (fun z : ℝ => (Real.exp (Real.log z/2):ℂ)*ψ (Real.log z)) y :=
      (Complex.ofRealCLM.contDiff.contDiffAt.comp y
        (Real.contDiff_exp.contDiffAt.comp y (hl.div_const 2))).mul (hψ.contDiffAt.comp y hl)
    apply he.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hp] with z hz
    exact ite_eq_left hz
  · have hy : y<Real.exp A := lt_of_le_of_lt (le_of_not_gt hp) (Real.exp_pos A)
    apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hy] with z hz
    exact inverseHalfDensityTest_zero_below ψ A B hs z hz

#print axioms logHalfDensity_inverse
#print axioms inverseHalfDensityTest_support
#print axioms inverseHalfDensityTest_smooth

end QuantitativeMaass
