module

public import QuantitativeMaassLocalCuspSmoothingV1
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory Matrix
open scoped Topology ContDiff MatrixGroups InnerProductSpace

namespace QuantitativeMaass.Wave

/-- A global smoothing assembled from the actual compatible local bands. -/
def cuspSmoothing (N : ℕ) (hN : 0<N) (s : SL(2,ℤ)) (A B : ℝ)
    (ψ : ℝ → ℂ) (hψ : Continuous ψ) (f : AutomorphicSpace N) (p : ℝ × ℝ) : ℂ :=
  localCuspSmoothing N hN s (p.2+A) (p.2+B) ψ hψ f p

theorem cuspSmoothing_eq_fixed (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B C D : ℝ) (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hs : Function.support ψ⊆Icc A B) (f : AutomorphicSpace N) (p : ℝ × ℝ)
    (hp : Icc (p.2+A) (p.2+B)⊆Icc C D) :
    cuspSmoothing N hN s A B ψ hψ.continuous f p=
      localCuspSmoothing N hN s C D ψ hψ.continuous f p :=
  cuspLogWaveTest_band_independent N hN s _ _ C D (fun y => ψ (y-p.2))
    (translatedTest_smooth ψ hψ p.2) (translatedTest_support ψ A B hs p.2)
    (Subset.trans (translatedTest_support ψ A B hs p.2) hp) f p.1

theorem cuspSmoothing_eventually_fixed (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B : ℝ) (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hs : Function.support ψ⊆Icc A B) (f : AutomorphicSpace N) (p : ℝ × ℝ) :
    cuspSmoothing N hN s A B ψ hψ.continuous f =ᶠ[𝓝 p]
      localCuspSmoothing N hN s (p.2+A-1) (p.2+B+1) ψ hψ.continuous f := by
  have hn : ∀ᶠ q : ℝ × ℝ in 𝓝 p, q.2∈Ioo (p.2-1) (p.2+1) :=
    continuous_snd.continuousAt (Ioo_mem_nhds (by linarith) (by linarith))
  filter_upwards [hn] with q hq
  apply cuspSmoothing_eq_fixed N hN s A B _ _ ψ hψ hs f q
  intro y hy
  constructor <;> linarith [hq.1,hq.2,hy.1,hy.2]

/-- Joint regularity of the GLOBAL smoothing, obtained by equality near
each point with a fixed-band L2 smoothing. -/
theorem cuspSmoothing_contDiff_two (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B : ℝ) (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hs : Function.support ψ⊆Icc A B)
    {f g : AutomorphicSpace N} (hfg : FriedrichsGraph N f g) :
    ContDiff ℝ 2 (cuspSmoothing N hN s A B ψ hψ.continuous f) := by
  have hcompact : HasCompactSupport ψ :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal hs isClosed_Icc)
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact (localCuspSmoothing_contDiff_two N hN s (p.2+A-1) (p.2+B+1)
    ψ hψ hcompact hfg).contDiffAt.congr_of_eventuallyEq
      (cuspSmoothing_eventually_fixed N hN s A B ψ hψ hs f p)

/-- Second derivative along a constant-velocity affine curve. -/
theorem second_deriv_along (u : ℝ × ℝ → ℂ) (hu : ContDiff ℝ 2 u)
    (c : ℝ → ℝ × ℝ) (v : ℝ × ℝ) (hc : ∀ r, HasDerivAt c v r) (t : ℝ) :
    deriv (deriv (fun r => u (c r))) t=fderiv ℝ (fderiv ℝ u) (c t) v v := by
  have hd := hu.differentiable (by norm_num)
  have hdd := (hu.fderiv_right (m:=1) (by norm_num)).differentiable one_ne_zero
  have he : deriv (fun r => u (c r))=fun r => fderiv ℝ u (c r) v :=
    funext (fun r => ((hd (c r)).hasFDerivAt.comp_hasDerivAt r (hc r)).deriv)
  rw [he]
  have h := ((hdd (c t)).hasFDerivAt.comp_hasDerivAt t (hc t)).clm_apply
    (hasDerivAt_const t v)
  simpa only [map_zero,add_zero,Function.comp_apply] using h.deriv

/-- The global smoothing satisfies the classical free-wave PDE. Its C2
regularity and both second derivatives have been proved from actual states. -/
theorem cuspSmoothing_PDE (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B : ℝ) (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hs : Function.support ψ⊆Icc A B)
    {f g : AutomorphicSpace N} (hfg : FriedrichsGraph N f g) (p : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (cuspSmoothing N hN s A B ψ hψ.continuous f)) p (1,0) (1,0)=
      fderiv ℝ (fderiv ℝ (cuspSmoothing N hN s A B ψ hψ.continuous f)) p (0,1) (0,1) := by
  let C := p.2+A-1
  let D := p.2+B+1
  let u := localCuspSmoothing N hN s C D ψ hψ.continuous f
  have hcompact : HasCompactSupport ψ :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal hs isClosed_Icc)
  have hu : ContDiff ℝ 2 u := localCuspSmoothing_contDiff_two N hN s C D ψ hψ hcompact hfg
  have he := (cuspSmoothing_eventually_fixed N hN s A B ψ hψ hs f p).fderiv (𝕜:=ℝ)
  rw [he.fderiv_eq]
  have ht := second_deriv_along u hu (fun t => (t,p.2)) (1,0)
    (fun t => (hasDerivAt_id t).prodMk (hasDerivAt_const t p.2)) p.1
  have hx := second_deriv_along u hu (fun x => (p.1,x)) (0,1)
    (fun x => (hasDerivAt_const x p.1).prodMk (hasDerivAt_id x)) p.2
  change fderiv ℝ (fderiv ℝ u) p (1,0) (1,0)=fderiv ℝ (fderiv ℝ u) p (0,1) (0,1)
  rw [← ht,← hx]
  have hsupport : Function.support (fun y => ψ (y-p.2))⊆Icc C D := by
    intro y hy
    have hm := translatedTest_support ψ A B hs p.2 hy
    constructor <;> dsimp [C,D] <;> linarith [hm.1,hm.2]
  exact (localCuspSmoothing_time_second N hN s C D ψ hψ f p.1 p.2 hsupport).deriv.trans
    (localCuspSmoothing_space_second N hN s C D ψ hψ hcompact f p.1 p.2).deriv.symm

#print axioms cuspSmoothing_contDiff_two
#print axioms cuspSmoothing_PDE

end QuantitativeMaass.Wave
