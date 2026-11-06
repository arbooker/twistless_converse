module

public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.Convex

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticEntireQuotient
open Complex Filter Set
open scoped Topology

theorem nonzero_germ (q : ℂ → ℂ) (hq : ∀ z, AnalyticAt ℂ q z)
    (hw : ∃ y, q y≠0) (x : ℂ) : ∀ᶠ z in 𝓝[≠] x, q z≠0 := by
  rcases (hq x).eventually_eq_zero_or_eventually_ne_zero with he|he
  · obtain ⟨y,hy⟩ := hw
    have ha : AnalyticOnNhd ℂ q univ := fun z _ => hq z
    exact False.elim (hy (ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ x) he (mem_univ y)))
  · exact he

/-- An exact identity with entire numerator and nonzero entire denominator
produces a normal-form meromorphic continuation, including agreement at
zeros of the denominator inside the original analytic half-plane. -/
theorem continuation (F q H : ℂ → ℂ) (bound : ℝ)
    (hF : ∀ z, AnalyticAt ℂ F z) (hq : ∀ z, AnalyticAt ℂ q z)
    (hw : ∃ y, q y≠0)
    (hH : ∀ z, bound<z.re → AnalyticAt ℂ H z)
    (he : ∀ z, bound<z.re → F z=q z*H z) :
    ∃ G : ℂ → ℂ, (∀ z, MeromorphicNFAt G z) ∧
      (∀ z, bound<z.re → G z=H z) ∧
      (∀ z, q z≠0 → AnalyticAt ℂ G z) ∧
      (∀ x, G=ᶠ[𝓝[≠] x] (fun z => F z/q z)) := by
  let Q : ℂ → ℂ := fun z => F z/q z
  have hQ : MeromorphicOn Q univ := fun z _ => (hF z).meromorphicAt.div (hq z).meromorphicAt
  let G := toMeromorphicNFOn Q univ
  have hG (z : ℂ) : MeromorphicNFAt G z := meromorphicNFOn_toMeromorphicNFOn Q univ (mem_univ z)
  have hg (z : ℂ) : G=ᶠ[𝓝[≠] z] Q := hQ.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z)
  refine ⟨G,hG,?_,?_,hg⟩
  · intro x hx
    have hn : ∀ᶠ z in 𝓝 x, bound<z.re :=
      (isOpen_lt continuous_const continuous_re).mem_nhds hx
    have hgh : G=ᶠ[𝓝[≠] x] H := by
      filter_upwards [hg x,nonzero_germ q hq hw x,hn.filter_mono nhdsWithin_le_nhds] with z hz hqz hB
      rw [hz]
      dsimp only [Q]
      rw [he z hB]
      exact mul_div_cancel_left₀ (H z) hqz
    exact (((hG x).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (hH x hx).meromorphicNFAt).mp hgh).eq_of_nhds
  · intro x hx
    have hQa : AnalyticAt ℂ Q x := (hF x).div (hq x) hx
    have hnear := ((hG x).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hQa.meromorphicNFAt).mp (hg x)
    exact (analyticAt_congr hnear).mpr hQa

#print axioms nonzero_germ
#print axioms continuation
end QuantitativeArithmeticEntireQuotient
