module

public import QuantitativeMaassAbelKernelGraphV1
public import Mathlib.Analysis.SpecialFunctions.Arcosh

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Lift a positive-time test through q=cosh(t), extended by zero below1. -/
def coshTestLift (ψ : ℝ → ℂ) (q : ℝ) : ℂ := if 1<q then ψ (Real.arcosh q) else 0

theorem coshTestLift_zero_below (ψ : ℝ → ℂ) (δ R : ℝ) (hδ : 0<δ)
    (hs : Function.support ψ⊆Icc δ R) {q : ℝ} (hq : q<Real.cosh δ) : coshTestLift ψ q=0 := by
  by_cases hq1 : 1<q
  · rw [coshTestLift,ite_eq_left hq1]
    by_contra hn
    have ht := (hs hn).1
    have hc : Real.cosh δ≤Real.cosh (Real.arcosh q) := by
      apply Real.cosh_le_cosh.mpr
      rw [abs_of_pos hδ,abs_of_nonneg (Real.arcosh_nonneg hq1.le)]
      exact ht
    rw [Real.cosh_arcosh hq1.le] at hc
    linarith
  · simp only [coshTestLift,ite_eq_right hq1]

theorem coshTestLift_support (ψ : ℝ → ℂ) (δ R : ℝ) (hδ : 0<δ) (hR : 0≤R)
    (hs : Function.support ψ⊆Icc δ R) :
    Function.support (coshTestLift ψ)⊆Icc (Real.cosh δ) (Real.cosh R) := by
  intro q hq
  change coshTestLift ψ q≠0 at hq
  have hq1 : 1<q := by
    by_contra hn
    exact hq (by simp [coshTestLift,hn])
  have hn : ψ (Real.arcosh q)≠0 := by simpa only [coshTestLift,ite_eq_left hq1] using hq
  have ht := hs hn
  have hlow : Real.cosh δ≤q := by
    rw [← Real.cosh_arcosh hq1.le]
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_pos hδ,abs_of_nonneg (Real.arcosh_nonneg hq1.le)]
    exact ht.1
  have hupp : q≤Real.cosh R := by
    rw [← Real.cosh_arcosh hq1.le]
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg hR,abs_of_nonneg (Real.arcosh_nonneg hq1.le)]
    exact ht.2
  exact ⟨hlow,hupp⟩

/-- Compact support away from time0 makes the zero extension smooth at q=1. -/
theorem coshTestLift_smooth (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (δ R : ℝ)
    (hδ : 0<δ) (hs : Function.support ψ⊆Icc δ R) : ContDiff ℝ ∞ (coshTestLift ψ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro q
  by_cases hq : 1<q
  · have he : coshTestLift ψ=ᶠ[𝓝 q] (fun v => ψ (Real.arcosh v)) := by
      filter_upwards [Ioi_mem_nhds hq] with v hv
      exact ite_eq_left hv
    exact (hψ.contDiffAt.comp q (Real.contDiffAt_arcosh hq)).congr_of_eventuallyEq he
  · have hb : q<Real.cosh δ := lt_of_le_of_lt (le_of_not_gt hq)
      (Real.one_lt_cosh.mpr (ne_of_gt hδ))
    have he : coshTestLift ψ=ᶠ[𝓝 q] (fun _ => (0:ℂ)) := by
      filter_upwards [Iio_mem_nhds hb] with v hv
      exact coshTestLift_zero_below ψ δ R hδ hs hv
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem coshTestLift_compact (ψ : ℝ → ℂ) (δ R : ℝ) (hδ : 0<δ) (hR : 0≤R)
    (hs : Function.support ψ⊆Icc δ R) : HasCompactSupport (coshTestLift ψ) :=
  (isCompact_Icc : IsCompact (Icc (Real.cosh δ) (Real.cosh R))).of_isClosed_subset isClosed_closure
    (closure_minimal (coshTestLift_support ψ δ R hδ hR hs) isClosed_Icc)

theorem coshTestLift_time (ψ : ℝ → ℂ) (δ R : ℝ) (hδ : 0<δ)
    (hs : Function.support ψ⊆Icc δ R) (t : ℝ) :
    coshTimeTest (coshTestLift ψ) t=ψ |t| := by
  by_cases ht : t=0
  · subst t
    have hz : ψ 0=0 := by
      by_contra hn
      have hh := (hs hn).1
      linarith
    simp [coshTimeTest,coshTestLift,hz]
  · have hc : 1<Real.cosh t := Real.one_lt_cosh.mpr ht
    have he : Real.arcosh (Real.cosh t)=|t| := by
      rw [← Real.cosh_abs t]
      exact Real.arcosh_cosh (abs_nonneg t)
    simp only [coshTimeTest,coshTestLift,ite_eq_left hc,he]

theorem coshTestLift_real (ψ : ℝ → ℂ) (hr : ∀ t,star (ψ t)=ψ t) (q : ℝ) :
    star (coshTestLift ψ q)=coshTestLift ψ q := by
  unfold coshTestLift
  split_ifs <;> simp [hr]

#print axioms coshTestLift_support
#print axioms coshTestLift_smooth
#print axioms coshTestLift_compact
#print axioms coshTestLift_time

end QuantitativeMaass
