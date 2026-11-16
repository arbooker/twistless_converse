module

public import QuantitativeMaassLocalWronskianV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Wave

/-- Cauchy representation on the closed positive half-line. The strong
curve is defined globally, but its equation and full Friedrichs graph are
only required at nonnegative times. The endpoint is included explicitly. -/
theorem wave_cauchy_pairing_nonneg (N : ℕ) (u v y : ℝ → AutomorphicSpace N)
    (hu : ∀ s,0≤s → HasDerivAt u (v s) s)
    (hv : ∀ s,0≤s → HasDerivAt v ((1/4:ℂ) • u s-y s) s)
    (hg : ∀ s,0≤s → FriedrichsGraph N (u s) (y s))
    {a b : AutomorphicSpace N} (hab : FriedrichsGraph N a b) (t : ℝ) (ht : 0≤t) :
    inner ℂ (u t) a=inner ℂ (v 0) (quotientSine N t a)+
      inner ℂ (u 0) (shiftedQuotientWave N t a) := by
  have hd (s : ℝ) (hs : 0≤s) : HasDerivAt (waveWronskian N u v a t) 0 s :=
    waveWronskian_hasDerivAt_of_point N u v y s (hu s hs) (hv s hs) (hg s hs) hab t
  have hc : ContinuousOn (waveWronskian N u v a t) (Icc 0 t) :=
    fun s hs => (hd s hs.1).continuousAt.continuousWithinAt
  have hr (s : ℝ) (hs : s∈Ico 0 t) :
      HasDerivWithinAt (waveWronskian N u v a t) 0 (Ici s) s :=
    (hd s hs.1).hasDerivWithinAt
  have he := constant_of_has_deriv_right_zero hc hr t ⟨ht,le_rfl⟩
  simpa only [waveWronskian,sub_self,sub_zero,quotientSine_zero,inner_zero_right,zero_add,
    shiftedQuotientWave_zero,ContinuousLinearMap.id_apply] using he

#print axioms wave_cauchy_pairing_nonneg

end QuantitativeMaass.Wave
