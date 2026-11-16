module

public import QuantitativeMaassCuspSmoothingV1
public import QuantitativeMaassClassicalDAlembertV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory Matrix
open scoped Topology ContDiff MatrixGroups InnerProductSpace

namespace QuantitativeMaass.Wave

theorem cuspSmoothing_initial_velocity (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B : ℝ) (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hs : Function.support ψ⊆Icc A B)
    {f g : AutomorphicSpace N} (hfg : FriedrichsGraph N f g) (x : ℝ) :
    fderiv ℝ (cuspSmoothing N hN s A B ψ hψ.continuous f) (0,x) (1,0)=0 := by
  let C := x+A-1
  let D := x+B+1
  let u := localCuspSmoothing N hN s C D ψ hψ.continuous f
  have hcompact : HasCompactSupport ψ :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal hs isClosed_Icc)
  have hu : ContDiff ℝ 2 u := localCuspSmoothing_contDiff_two N hN s C D ψ hψ hcompact hfg
  have he := (cuspSmoothing_eventually_fixed N hN s A B ψ hψ hs f (0,x)).fderiv_eq (𝕜:=ℝ)
  rw [he]
  have ht := (hu.differentiable (by norm_num) (0,x)).hasFDerivAt.comp_hasDerivAt 0
    ((hasDerivAt_id (0:ℝ)).prodMk (hasDerivAt_const (0:ℝ) x))
  change fderiv ℝ u (0,x) (1,0)=0
  rw [← ht.deriv]
  have hsupport : Function.support (fun y => ψ (y-x))⊆Icc C D := by
    intro y hy
    have hm := translatedTest_support ψ A B hs x hy
    constructor <;> dsimp [C,D] <;> linarith [hm.1,hm.2]
  exact cuspLogWaveTest_initial_velocity N hN s C D (fun y => ψ (y-x))
    (translatedTest_smooth ψ hψ x) hsupport f

/-- D'Alembert's formula for the actual cusp smoothing, initially on the
dense Friedrichs domain. Joint regularity and the PDE are theorems above. -/
theorem cuspSmoothing_dAlembert_domain (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B : ℝ) (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hs : Function.support ψ⊆Icc A B)
    {f g : AutomorphicSpace N} (hfg : FriedrichsGraph N f g) (t x : ℝ) :
    cuspSmoothing N hN s A B ψ hψ.continuous f (t,x)=
      (cuspSmoothing N hN s A B ψ hψ.continuous f (0,x+t)+
        cuspSmoothing N hN s A B ψ hψ.continuous f (0,x-t))/2 :=
  classical_wave_dAlembert _ (cuspSmoothing_contDiff_two N hN s A B ψ hψ hs hfg)
    (cuspSmoothing_PDE N hN s A B ψ hψ hs hfg)
    (cuspSmoothing_initial_velocity N hN s A B ψ hψ hs hfg) t x

theorem cuspSmoothing_continuous_initial (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B : ℝ) (ψ : ℝ → ℂ) (hψ : Continuous ψ) (p : ℝ × ℝ) :
    Continuous (fun f : AutomorphicSpace N => cuspSmoothing N hN s A B ψ hψ f p) :=
  continuous_const.inner ((cuspLogConstant N hN s (p.2+A) (p.2+B)).continuous.comp
    (shiftedQuotientWave N p.1).continuous)

/-- The actual all-cusp free-wave formula against EVERY smooth compact
test, for arbitrary quotient L2 initial states. This extends the proved
classical formula by the actual resolvent's dense range. -/
theorem cuspSmoothing_dAlembert (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B : ℝ) (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hs : Function.support ψ⊆Icc A B) (f : AutomorphicSpace N) (t x : ℝ) :
    cuspSmoothing N hN s A B ψ hψ.continuous f (t,x)=
      (cuspSmoothing N hN s A B ψ hψ.continuous f (0,x+t)+
        cuspSmoothing N hN s A B ψ hψ.continuous f (0,x-t))/2 := by
  have he : (fun f : AutomorphicSpace N => cuspSmoothing N hN s A B ψ hψ.continuous f (t,x))=
      fun f => (cuspSmoothing N hN s A B ψ hψ.continuous f (0,x+t)+
        cuspSmoothing N hN s A B ψ hψ.continuous f (0,x-t))/2 := by
    apply (friedrichsResolvent_denseRange N).equalizer
      (cuspSmoothing_continuous_initial N hN s A B ψ hψ.continuous (t,x))
      (((cuspSmoothing_continuous_initial N hN s A B ψ hψ.continuous (0,x+t)).add
        (cuspSmoothing_continuous_initial N hN s A B ψ hψ.continuous (0,x-t))).div_const 2)
    funext z
    exact cuspSmoothing_dAlembert_domain N hN s A B ψ hψ hs (friedrichsGraph_resolvent N z) t x
  exact congrFun he f

#print axioms cuspSmoothing_initial_velocity
#print axioms cuspSmoothing_dAlembert_domain
#print axioms cuspSmoothing_dAlembert

end QuantitativeMaass.Wave
