module

public import QuantitativeMaassAbelKernelGraphV1
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- A concrete smooth compact cutoff that decreases above q=1. -/
def abelCutoffReal (a q : ℝ) : ℝ :=
  Real.smoothTransition (q+1)*(1-Real.smoothTransition ((q-1)/a))

def abelCutoff (a q : ℝ) : ℂ := abelCutoffReal a q

theorem abelCutoffReal_smooth (a : ℝ) : ContDiff ℝ ∞ (abelCutoffReal a) := by
  unfold abelCutoffReal
  fun_prop

theorem abelCutoff_smooth (a : ℝ) : ContDiff ℝ ∞ (abelCutoff a) :=
  Complex.ofRealCLM.contDiff.comp (abelCutoffReal_smooth a)

theorem abelCutoffReal_nonneg (a q : ℝ) : 0≤abelCutoffReal a q :=
  mul_nonneg (Real.smoothTransition.nonneg _) (sub_nonneg.mpr (Real.smoothTransition.le_one _))

theorem abelCutoffReal_one (a : ℝ) : abelCutoffReal a 1=1 := by
  simp [abelCutoffReal]

theorem abelCutoff_support_interval (a : ℝ) (ha : 0<a) :
    Function.support (abelCutoff a)⊆Icc (-1) (1+a) := by
  intro q hq
  have hn : abelCutoffReal a q≠0 := by
    intro h
    exact hq (by simp [abelCutoff,h])
  constructor
  · by_contra h
    have hz := Real.smoothTransition.zero_of_nonpos (show q+1≤0 by linarith)
    exact hn (by simp [abelCutoffReal,hz])
  · by_contra h
    have hh : 1≤(q-1)/a := (le_div_iff₀ ha).mpr (by linarith)
    exact hn (by simp [abelCutoffReal,Real.smoothTransition.one_of_one_le hh])

theorem abelCutoff_support (a : ℝ) (ha : 0<a) :
    Function.support (abelCutoff a)⊆Iic (1+a) := fun _ h => (abelCutoff_support_interval a ha h).2

theorem abelCutoff_compact (a : ℝ) (ha : 0<a) : HasCompactSupport (abelCutoff a) :=
  (isCompact_Icc : IsCompact (Icc (-1:ℝ) (1+a))).of_isClosed_subset isClosed_closure
    (closure_minimal (abelCutoff_support_interval a ha) isClosed_Icc)

/-- Above q=1 the left cutoff is constant and the right cutoff decreases. -/
theorem abelCutoffReal_deriv_nonpos (a : ℝ) (ha : 0<a) (q : ℝ) (hq : 1≤q) :
    deriv (abelCutoffReal a) q≤0 := by
  have he : abelCutoffReal a=ᶠ[𝓝 q] (fun v => 1-Real.smoothTransition ((v-1)/a)) := by
    filter_upwards [Ioi_mem_nhds (show 0<q by linarith)] with v hv
    have hv' : 0<v := hv
    simp [abelCutoffReal,Real.smoothTransition.one_of_one_le (show 1≤v+1 by linarith)]
  rw [he.deriv_eq]
  apply Antitone.deriv_nonpos
  intro x y hxy
  exact sub_le_sub_left (Real.smoothTransition.monotone (div_le_div_of_nonneg_right
    (sub_le_sub_right hxy 1) ha.le)) 1

theorem abelCutoff_deriv (a q : ℝ) :
    deriv (abelCutoff a) q=((deriv (abelCutoffReal a) q:ℝ):ℂ) :=
  (((abelCutoffReal_smooth a).differentiable (by simp) q).hasDerivAt.ofReal_comp).deriv

#print axioms abelCutoff_smooth
#print axioms abelCutoff_support_interval
#print axioms abelCutoff_compact
#print axioms abelCutoffReal_deriv_nonpos
#print axioms abelCutoff_deriv

end QuantitativeMaass
