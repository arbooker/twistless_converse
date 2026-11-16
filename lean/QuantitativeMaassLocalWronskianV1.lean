module

public import QuantitativeMaassWaveWronskianV1

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Wave

open QuantitativeArithmeticMaassWave

private theorem localShiftedWronskian_cancel {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (u v y s g w : H) (hs : inner ℂ y s=inner ℂ u g) :
    (inner ℂ v (-w)+inner ℂ ((1/4 : ℂ) • u-y) s)+
      (inner ℂ u (-((1/4 : ℂ) • s-g))+inner ℂ v w)=0 := by
  simp only [inner_neg_right,inner_sub_left,inner_sub_right,inner_smul_left,
    inner_smul_right,map_div₀,map_one,map_ofNat,hs]
  ring

/-- The dual Wronskian derivative only needs the strong equation and the
Friedrichs graph at the point being differentiated. -/
theorem waveWronskian_hasDerivAt_of_point (N : ℕ) (u v y : ℝ → AutomorphicSpace N)
    (s : ℝ) (hu : HasDerivAt u (v s) s)
    (hv : HasDerivAt v ((1/4:ℂ) • u s-y s) s)
    (hg : FriedrichsGraph N (u s) (y s))
    {a b : AutomorphicSpace N} (hab : FriedrichsGraph N a b) (t : ℝ) :
    HasDerivAt (waveWronskian N u v a t) 0 s := by
  have hS : HasDerivAt (fun r => quotientSine N (t-r) a)
      (-shiftedQuotientWave N (t-s) a) s := by
    simpa only [Function.comp_def,id_eq,neg_smul,one_smul] using
      (quotientSine_hasDerivAt N a (t-s)).scomp s ((hasDerivAt_id s).const_sub t)
  have hW : HasDerivAt (fun r => shiftedQuotientWave N (t-r) a)
      (-quotientWaveVelocity N a b (t-s)) s := by
    simpa only [Function.comp_def,id_eq,neg_smul,one_smul] using
      (quotientWave_hasDerivAt N hab (t-s)).scomp s ((hasDerivAt_id s).const_sub t)
  have h := (hv.inner ℂ hS).add (hu.inner ℂ hW)
  rw [quotientWaveVelocity_eq_sine] at h
  exact h.congr_deriv (localShiftedWronskian_cancel _ _ _ _ _ _
    (friedrichsGraph_symmetric N hg (quotientSine_graph N hab (t-s))))

/-- Wronskian conservation on any connected open time interval. No equation
outside that interval is required. -/
theorem waveWronskian_constant_on (N : ℕ) (u v y : ℝ → AutomorphicSpace N)
    (S : Set ℝ) (ho : IsOpen S) (hc : IsPreconnected S)
    (hu : ∀ s∈S,HasDerivAt u (v s) s)
    (hv : ∀ s∈S,HasDerivAt v ((1/4:ℂ) • u s-y s) s)
    (hg : ∀ s∈S,FriedrichsGraph N (u s) (y s))
    {a b : AutomorphicSpace N} (hab : FriedrichsGraph N a b)
    (t s r : ℝ) (hs : s∈S) (hr : r∈S) :
    waveWronskian N u v a t s=waveWronskian N u v a t r := by
  apply ho.is_const_of_deriv_eq_zero hc
  · intro z hz
    exact (waveWronskian_hasDerivAt_of_point N u v y z (hu z hz) (hv z hz)
      (hg z hz) hab t).differentiableAt.differentiableWithinAt
  · intro z hz
    exact (waveWronskian_hasDerivAt_of_point N u v y z (hu z hz) (hv z hz)
      (hg z hz) hab t).deriv
  · exact hs
  · exact hr

/-- Zero Cauchy data determine a strong shifted-wave solution on a connected
open interval containing the initial time. -/
theorem shiftedWave_zero_cauchy_unique_on (N : ℕ) (u v y : ℝ → AutomorphicSpace N)
    (S : Set ℝ) (ho : IsOpen S) (hc : IsPreconnected S)
    (hu : ∀ s∈S,HasDerivAt u (v s) s)
    (hv : ∀ s∈S,HasDerivAt v ((1/4:ℂ) • u s-y s) s)
    (hg : ∀ s∈S,FriedrichsGraph N (u s) (y s))
    (r : ℝ) (hr : r∈S) (hur : u r=0) (hvr : v r=0) (t : ℝ) (ht : t∈S) : u t=0 := by
  have htest (a b : AutomorphicSpace N) (hab : FriedrichsGraph N a b) :
      inner ℂ (u t) a=0 := by
    have h := waveWronskian_constant_on N u v y S ho hc hu hv hg hab t t r ht hr
    simpa only [waveWronskian,sub_self,quotientSine_zero,inner_zero_right,
      zero_add,shiftedQuotientWave_zero,ContinuousLinearMap.id_apply,
      hur,hvr,inner_zero_left,add_zero] using h
  have he : (fun a : AutomorphicSpace N => inner ℂ (u t) a)=fun _ => (0:ℂ) := by
    apply (friedrichsResolvent_denseRange N).equalizer
      (continuous_const.inner continuous_id) continuous_const
    funext z
    exact htest _ _ (friedrichsGraph_resolvent N z)
  exact inner_self_eq_zero.mp (congrFun he (u t))

#print axioms waveWronskian_hasDerivAt_of_point
#print axioms waveWronskian_constant_on
#print axioms shiftedWave_zero_cauchy_unique_on

end QuantitativeMaass.Wave
