module
public import SmallLevelContinuationTheoryV4
public import Mathlib.Analysis.Analytic.IsolatedZeros
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticAnalyticDivisorContinuation
open Complex Filter Set
open scoped Topology

/-- Nonvanishing at one point excludes the identically-zero alternative for
each of a finite collection of entire pivot functions. -/
theorem nonzero_germ {ι : Type*} [Fintype ι] (P : ι → ℂ → ℂ)
    (hP : ∀ i z, AnalyticAt ℂ (P i) z) (x : ℂ) (hx : ∀ i, P i x≠0)
    (y : ℂ) : ∀ᶠ z in 𝓝[≠] y, ∀ i, P i z≠0 := by
  apply Filter.eventually_all.mpr
  intro i
  rcases (hP i y).eventually_eq_zero_or_eventually_ne_zero with hzero|hne
  · have hglobal : AnalyticOnNhd ℂ (P i) Set.univ := fun z _ => hP i z
    have he := hglobal.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ y) hzero
    exact False.elim (hx i (he (Set.mem_univ x)))
  · exact hne

/-- A meromorphic identity known on an initial half-plane away from finitely
many entire pivot divisors continues to any point where those pivots are
nonzero. No nonvanishing bound on the whole initial half-plane is needed. -/
theorem halfplane_identity {ι : Type*} [Fintype ι] (P : ι → ℂ → ℂ)
    (hP : ∀ i z, AnalyticAt ℂ (P i) z) (x : ℂ) (hPx : ∀ i, P i x≠0)
    {F G : ℂ → ℂ} (b c : ℝ)
    (hF : MeromorphicOn F {z : ℂ | b<z.re})
    (hG : MeromorphicOn G {z : ℂ | b<z.re})
    (he : ∀ z : ℂ, c<z.re → (∀ i, P i z≠0) → F z=G z)
    (hx : b<x.re) : F=ᶠ[𝓝[≠] x] G := by
  let y : ℂ := ((max b c+1:ℝ):ℂ)
  have hyb : b<y.re := by dsimp [y]; linarith [le_max_left b c]
  have hyc : c<y.re := by dsimp [y]; linarith [le_max_right b c]
  have hn : ∀ᶠ z in 𝓝 y, c<z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hyc
  have htop : meromorphicOrderAt (fun z => F z-G z) y=⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds,nonzero_germ P hP x hPx y] with z hz hp
    exact sub_eq_zero.mpr (he z hz hp)
  have hxorder := (hF.sub hG).meromorphicOrderAt_eq_top_of_isPreconnected
    (convex_halfSpace_re_gt b).isPreconnected hyb hx htop
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp hxorder] with z hz
  exact sub_eq_zero.mp hz
#print axioms nonzero_germ
#print axioms halfplane_identity
end QuantitativeArithmeticAnalyticDivisorContinuation
