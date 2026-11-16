module

public import QuantitativeMaassPositiveTimeWaveV1
public import QuantitativeMaassLocalWronskianV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace QuantitativeMaass

/-- Exact Cauchy representation of the geometric translated-test curve,
paired against every vector in the full Friedrichs domain. The initial
position and velocity are the actual Abel operators of ψ and -ψ'. -/
theorem positiveTimeAbelOperator_cauchy_pairing (N : ℕ) [NeZero N]
    (ψ : PositiveTimeTest) (f : AutomorphicSpace N)
    {a b : AutomorphicSpace N} (hab : FriedrichsGraph N a b)
    (t : ℝ) (ht : 0<ψ.left+t) :
    inner ℂ (translatedPositiveTimeAbelOperator N ψ t f) a=
      inner ℂ (-positiveTimeAbelOperator N ψ.first f) (Wave.quotientSine N t a)+
      inner ℂ (positiveTimeAbelOperator N ψ f) (Wave.shiftedQuotientWave N t a) := by
  let u := fun s => translatedPositiveTimeAbelOperator N ψ s f
  let v := fun s => -translatedPositiveTimeAbelOperator N ψ.first s f
  let y := fun s => (1/4:ℂ) • u s-translatedPositiveTimeAbelOperator N ψ.second s f
  have hu (s : ℝ) (hs : s∈Ioi (-ψ.left)) : HasDerivAt u (v s) s :=
    translatedPositiveTimeAbelOperator_hasDerivAt_apply N ψ f s (by
      simp only [mem_Ioi] at hs; linarith)
  have hv (s : ℝ) (hs : s∈Ioi (-ψ.left)) :
      HasDerivAt v ((1/4:ℂ) • u s-y s) s := by
    have h := translatedPositiveTimeAbelOperator_velocity_hasDerivAt N ψ f s (by
      simp only [mem_Ioi] at hs; linarith)
    simpa only [y,sub_sub_cancel] using h
  have hg (s : ℝ) (hs : s∈Ioi (-ψ.left)) : FriedrichsGraph N (u s) (y s) :=
    translatedPositiveTimeAbelOperator_graph N ψ f s (by
      simp only [mem_Ioi] at hs; linarith)
  have h := Wave.waveWronskian_constant_on N u v y (Ioi (-ψ.left)) isOpen_Ioi
    isPreconnected_Ioi hu hv hg hab t t 0 (by simp only [mem_Ioi]; linarith)
    (by simp only [mem_Ioi]; have hp := ψ.left_pos; linarith)
  simpa only [Wave.waveWronskian,u,v,sub_self,sub_zero,Wave.quotientSine_zero,
    inner_zero_right,zero_add,Wave.shiftedQuotientWave_zero,ContinuousLinearMap.id_apply,
    translatedPositiveTimeAbelOperator_zero] using h

#print axioms positiveTimeAbelOperator_cauchy_pairing

end QuantitativeMaass
