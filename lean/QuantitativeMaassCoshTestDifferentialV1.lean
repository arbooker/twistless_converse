module

public import QuantitativeMaassCoshTestLiftV1

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem second_deriv_support_interval (ψ : ℝ → ℂ) (a b : ℝ)
    (hs : Function.support ψ⊆Icc a b) : Function.support (deriv (deriv ψ))⊆Icc a b :=
  support_deriv_subset.trans (tsupport_deriv_subset.trans (closure_minimal hs isClosed_Icc))

/-- On positive time, the q-coordinate differential expression is exactly
the ordinary second time derivative of the original test. -/
theorem coshTestLift_time_second (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (δ R : ℝ)
    (hδ : 0<δ) (hs : Function.support ψ⊆Icc δ R) (t : ℝ) (ht : 0<t) :
    coshTimeOperator (coshTestLift ψ) (Real.cosh t)=deriv (deriv ψ) t := by
  have he : coshTimeTest (coshTestLift ψ)=ᶠ[𝓝 t] ψ := by
    filter_upwards [Ioi_mem_nhds ht] with s hs0
    rw [coshTestLift_time ψ δ R hδ hs s,abs_of_pos hs0]
  have hd := coshTimeTest_second (coshTestLift ψ) (coshTestLift_smooth ψ hψ δ R hδ hs) t
  rw [he.deriv.deriv_eq] at hd
  exact hd.symm

/-- The time differential intertwining is global in q, including the
zero-extension region and its boundary. -/
theorem coshTestLift_operator (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (δ R : ℝ)
    (hδ : 0<δ) (hs : Function.support ψ⊆Icc δ R) :
    coshTimeOperator (coshTestLift ψ)=coshTestLift (deriv (deriv ψ)) := by
  funext q
  by_cases hq : 1<q
  · have h := coshTestLift_time_second ψ hψ δ R hδ hs (Real.arcosh q) (Real.arcosh_pos hq)
    rw [Real.cosh_arcosh hq.le] at h
    simpa only [coshTestLift,ite_eq_left hq] using h
  · have hb : q<Real.cosh δ := lt_of_le_of_lt (le_of_not_gt hq)
      (Real.one_lt_cosh.mpr (ne_of_gt hδ))
    have he : coshTestLift ψ=ᶠ[𝓝 q] (fun _ => (0:ℂ)) := by
      filter_upwards [Iio_mem_nhds hb] with v hv
      exact coshTestLift_zero_below ψ δ R hδ hs hv
    have hd1 : deriv (coshTestLift ψ) q=0 := by simpa using he.deriv_eq
    have hd2 : deriv (deriv (coshTestLift ψ)) q=0 := by simpa using he.deriv.deriv_eq
    simp [coshTimeOperator,hd1,hd2,coshTestLift,hq]

#print axioms second_deriv_support_interval
#print axioms coshTestLift_time_second
#print axioms coshTestLift_operator

end QuantitativeMaass
