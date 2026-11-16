module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- A smooth compact partition for one-period integration, supported in
[0,2]. Its two translates sum to one on [0,1]. -/
def periodCutoff (x : ℝ) : ℝ := Real.smoothTransition x-Real.smoothTransition (x-1)

theorem periodCutoff_smooth : ContDiff ℝ ∞ periodCutoff :=
  Real.smoothTransition.contDiff.sub
    (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))

theorem periodCutoff_support : tsupport periodCutoff⊆Icc (0:ℝ) 2 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hn
  simp only [mem_Icc,not_and_or,not_le] at hn
  rcases hn with hn | hn
  · exact hx (by simp only [periodCutoff,Real.smoothTransition.zero_of_nonpos hn.le,
      Real.smoothTransition.zero_of_nonpos (show x-1≤0 by linarith),sub_self])
  · exact hx (by simp only [periodCutoff,Real.smoothTransition.one_of_one_le (show 1≤x by linarith),
      Real.smoothTransition.one_of_one_le (show 1≤x-1 by linarith),sub_self])

theorem periodCutoff_compact : HasCompactSupport periodCutoff :=
  isCompact_Icc.of_isClosed_subset isClosed_closure periodCutoff_support

theorem periodCutoff_partition (x : ℝ) (hx : x∈Icc (0:ℝ) 1) :
    periodCutoff x+periodCutoff (x+1)=1 := by
  simp only [periodCutoff,Real.smoothTransition.zero_of_nonpos (show x-1≤0 by linarith [hx.2]),
    Real.smoothTransition.one_of_one_le (show 1≤x+1 by linarith [hx.1]),add_sub_cancel_right]
  ring

/-- Differentiating a constant translate sum on a closed period interval.
Endpoint values follow by continuity, so the statement is pointwise. -/
theorem derivative_translate_sum (w : ℝ → ℝ) (hw : Differentiable ℝ w)
    (hwd : Continuous (deriv w)) (C : ℝ)
    (hp : ∀ x∈Icc (0:ℝ) 1, w x+w (x+1)=C) :
    ∀ x∈Icc (0:ℝ) 1, deriv w x+deriv w (x+1)=0 := by
  have he : EqOn (fun x => deriv w x+deriv w (x+1)) (fun _ => 0) (Ioo (0:ℝ) 1) := by
    intro x hx
    have hl : (fun y => w y+w (y+1))=ᶠ[𝓝 x] fun _ => C := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact hp y ⟨hy.1.le,hy.2.le⟩
    have hd := (hw x).hasDerivAt.add
      ((hw (x+1)).hasDerivAt.comp x ((hasDerivAt_id x).add_const 1))
    have hd' := hd.congr_of_eventuallyEq hl.symm
    have h := hd'.deriv
    simpa only [deriv_const,mul_one] using h.symm
  have hc := he.closure
    (hwd.add (hwd.comp (continuous_id.add continuous_const)))
    continuous_const
  rw [closure_Ioo (show (0:ℝ)≠1 by norm_num)] at hc
  exact hc

theorem periodCutoff_deriv_partition (x : ℝ) (hx : x∈Icc (0:ℝ) 1) :
    deriv periodCutoff x+deriv periodCutoff (x+1)=0 :=
  derivative_translate_sum periodCutoff (periodCutoff_smooth.differentiable (by simp))
    (periodCutoff_smooth.continuous_deriv (by simp)) 1 periodCutoff_partition x hx

theorem periodCutoff_second_partition (x : ℝ) (hx : x∈Icc (0:ℝ) 1) :
    deriv (deriv periodCutoff) x+deriv (deriv periodCutoff) (x+1)=0 := by
  have hd : ContDiff ℝ ∞ (deriv periodCutoff) := (contDiff_infty_iff_deriv.mp periodCutoff_smooth).2
  exact derivative_translate_sum (deriv periodCutoff) (hd.differentiable (by simp))
    (hd.continuous_deriv (by simp)) 0 periodCutoff_deriv_partition x hx

/-- A two-period weighted integral reduces to the translate sum of its
weight on one period. This is the horizontal cancellation used in weak PDE tests. -/
theorem periodic_weight_integral (w : ℝ → ℝ) (hw : Continuous w)
    (F : ℝ → ℂ) (hF : Continuous F) (hperiod : Function.Periodic F 1) :
    (∫ x in (0:ℝ)..2, w x • F x)=
      ∫ x in (0:ℝ)..1, (w x+w (x+1)) • F x := by
  have hc : Continuous (fun x => w x • F x) := hw.smul hF
  have ht : (∫ x in (1:ℝ)..2, w x • F x)=
      ∫ x in (0:ℝ)..1, w (x+1) • F x := by
    have he := intervalIntegral.integral_comp_add_right (fun x => w x • F x)
      (a := (0:ℝ)) (b := 1) 1
    norm_num only [zero_add,one_add_one_eq_two] at he
    rw [← he]
    apply intervalIntegral.integral_congr
    intro x _
    change w (x+1) • F (x+1)=w (x+1) • F x
    rw [hperiod x]
  have htc : Continuous (fun x => w (x+1) • F x) :=
    (hw.comp (continuous_id.add continuous_const)).smul hF
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 1)
    (hc.intervalIntegrable 1 2),ht,← intervalIntegral.integral_add (hc.intervalIntegrable 0 1)
      (htc.intervalIntegrable 0 1)]
  apply intervalIntegral.integral_congr
  intro x _
  exact (add_smul _ _ _).symm

theorem periodCutoff_integral (F : ℝ → ℂ) (hF : Continuous F) (hperiod : Function.Periodic F 1) :
    (∫ x in (0:ℝ)..2, periodCutoff x • F x)=∫ x in (0:ℝ)..1, F x := by
  rw [periodic_weight_integral periodCutoff periodCutoff_smooth.continuous F hF hperiod]
  apply intervalIntegral.integral_congr
  intro x hx
  change (periodCutoff x+periodCutoff (x+1)) • F x=F x
  rw [periodCutoff_partition x (by simpa using hx),one_smul]

theorem periodCutoff_second_integral (F : ℝ → ℂ) (hF : Continuous F)
    (hperiod : Function.Periodic F 1) :
    (∫ x in (0:ℝ)..2, deriv (deriv periodCutoff) x • F x)=0 := by
  have hd : ContDiff ℝ ∞ (deriv periodCutoff) := (contDiff_infty_iff_deriv.mp periodCutoff_smooth).2
  rw [periodic_weight_integral _ (hd.continuous_deriv (by simp)) F hF hperiod]
  have he : (∫ x in (0:ℝ)..1, (deriv (deriv periodCutoff) x+
      deriv (deriv periodCutoff) (x+1)) • F x)=∫ _ in (0:ℝ)..1, (0:ℂ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    change (deriv (deriv periodCutoff) x+deriv (deriv periodCutoff) (x+1)) • F x=0
    rw [periodCutoff_second_partition x (by simpa using hx),zero_smul]
  rw [he,intervalIntegral.integral_zero]

#print axioms periodCutoff_compact
#print axioms periodCutoff_second_partition
#print axioms periodCutoff_integral
#print axioms periodCutoff_second_integral

end QuantitativeMaass
