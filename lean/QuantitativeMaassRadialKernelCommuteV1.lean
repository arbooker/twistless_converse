module

public import QuantitativeMaassRadialKernelGraphV1
public import QuantitativeMaassShiftedWaveCommuteV1

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set
open scoped Topology ContDiff

namespace QuantitativeMaass

variable (N : ℕ) [NeZero N] (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
  (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
  (hr : ∀ q,star (g q)=g q)
include hr

/-- Resolvent commutation is derived from the actual full-domain graph
identity of the radial operator. -/
theorem radialKernelOperator_commute_resolvent :
    Commute (radialKernelOperator N g hg R hR hs) (friedrichsResolvent N) := by
  apply ContinuousLinearMap.ext
  intro f
  let K := radialKernelOperator N g hg R hR hs
  have h := radialKernelOperator_graph N g hg R hR hs hr (friedrichsResolvent N f)
  have he := radialKernelOperator_on_graph N g hg R hR hs hr (friedrichsGraph_resolvent N f)
  change K (f-friedrichsResolvent N f)=_ at he
  rw [← he] at h
  change friedrichsResolvent N (K (friedrichsResolvent N f)+K (f-friedrichsResolvent N f))=
    K (friedrichsResolvent N f) at h
  rw [map_sub,add_sub_cancel] at h
  exact h.symm

/-- Every wave time commutes with the geometric radial integral operator,
by the already constructed functional calculus of the actual resolvent. -/
theorem radialKernelOperator_commute_wave (t : ℝ) :
    Commute (radialKernelOperator N g hg R hR hs) (Wave.shiftedQuotientWave N t) :=
  Wave.shiftedQuotientWave_commute_of_resolvent N _
    (radialKernelOperator_commute_resolvent N g hg R hR hs hr) t

#print axioms radialKernelOperator_commute_resolvent
#print axioms radialKernelOperator_commute_wave

end QuantitativeMaass
