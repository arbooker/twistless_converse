module

public import QuantitativeMaassWaveSinePrimitiveV1
public import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Wave

open QuantitativeArithmeticMaassWave

private theorem shiftedWronskian_cancel {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (u v y s g w : H) (hs : inner ℂ y s=inner ℂ u g) :
    (inner ℂ v (-w)+inner ℂ ((1/4 : ℂ) • u-y) s)+
      (inner ℂ u (-((1/4 : ℂ) • s-g))+inner ℂ v w)=0 := by
  simp only [inner_neg_right,inner_sub_left,inner_sub_right,inner_smul_left,
    inner_smul_right,map_div₀,map_one,map_ofNat,hs]
  ring

/-- A dual Wronskian, with a backwards sine solution as the test vector. -/
def waveWronskian (N : ℕ) (u v : ℝ → AutomorphicSpace N)
    (a : AutomorphicSpace N) (t s : ℝ) : ℂ :=
  inner ℂ (v s) (quotientSine N (t-s) a)+
    inner ℂ (u s) (shiftedQuotientWave N (t-s) a)

/-- Symmetry of the actual Friedrichs graph makes the dual Wronskian constant.
No differentiability of the unknown in the form norm is assumed. -/
theorem waveWronskian_hasDerivAt (N : ℕ) (u v y : ℝ → AutomorphicSpace N)
    (hu : ∀ s, HasDerivAt u (v s) s)
    (hv : ∀ s, HasDerivAt v ((1/4 : ℂ) • u s-y s) s)
    (hg : ∀ s, FriedrichsGraph N (u s) (y s))
    {a b : AutomorphicSpace N} (hab : FriedrichsGraph N a b) (t s : ℝ) :
    HasDerivAt (waveWronskian N u v a t) 0 s := by
  have hS : HasDerivAt (fun r => quotientSine N (t-r) a)
      (-shiftedQuotientWave N (t-s) a) s := by
    simpa only [Function.comp_def,id_eq,neg_smul,one_smul] using
      (quotientSine_hasDerivAt N a (t-s)).scomp s ((hasDerivAt_id s).const_sub t)
  have hW : HasDerivAt (fun r => shiftedQuotientWave N (t-r) a)
      (-quotientWaveVelocity N a b (t-s)) s := by
    simpa only [Function.comp_def,id_eq,neg_smul,one_smul] using
      (quotientWave_hasDerivAt N hab (t-s)).scomp s ((hasDerivAt_id s).const_sub t)
  have h := ((hv s).inner ℂ hS).add ((hu s).inner ℂ hW)
  rw [quotientWaveVelocity_eq_sine] at h
  exact h.congr_deriv (shiftedWronskian_cancel _ _ _ _ _ _
    (friedrichsGraph_symmetric N (hg s) (quotientSine_graph N hab (t-s))))

theorem waveWronskian_constant (N : ℕ) (u v y : ℝ → AutomorphicSpace N)
    (hu : ∀ s, HasDerivAt u (v s) s)
    (hv : ∀ s, HasDerivAt v ((1/4 : ℂ) • u s-y s) s)
    (hg : ∀ s, FriedrichsGraph N (u s) (y s))
    {a b : AutomorphicSpace N} (hab : FriedrichsGraph N a b) (t s : ℝ) :
    waveWronskian N u v a t s=waveWronskian N u v a t 0 :=
  is_const_of_deriv_eq_zero
    (fun r => (waveWronskian_hasDerivAt N u v y hu hv hg hab t r).differentiableAt)
    (fun r => (waveWronskian_hasDerivAt N u v y hu hv hg hab t r).deriv) s 0

#print axioms waveWronskian_hasDerivAt
#print axioms waveWronskian_constant

end QuantitativeMaass.Wave
