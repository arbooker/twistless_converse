module
public import SmallLevelContinuationTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticMeromorphicModels
open Complex Filter Set
open scoped Topology

/-- Normalize and glue genuine meromorphic models agreeing with an analytic
initial function. No compatibility assumption between models is needed. -/
theorem glue (B : ℝ) (F : ℂ → ℂ) (H : ℕ → ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F {s : ℂ | B<s.re})
    (hH : ∀ M : ℕ, MeromorphicOn (H M) {s : ℂ | B-(M:ℝ)<s.re})
    (hHF : ∀ M : ℕ, EqOn (H M) F {s : ℂ | B<s.re}) :
    ∃ G : ℂ → ℂ, (∀ s, MeromorphicNFAt G s) ∧
      EqOn G F {s : ℂ | B<s.re} := by
  apply SmallLevelContinuation.halfplane_glue B F
  intro M
  let U := {s : ℂ | B-(M:ℝ)<s.re}
  refine ⟨toMeromorphicNFOn (H M) U,meromorphicNFOn_toMeromorphicNFOn _ _,?_⟩
  intro s hs
  have he : H M=ᶠ[𝓝 s] F := by
    have ht : ∀ᶠ z in 𝓝 s, B<z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
    filter_upwards [ht] with z hz
    exact hHF M hz
  have ha : AnalyticAt ℂ (H M) s := (analyticAt_congr he).mpr (hF s hs)
  have hU : s∈U := by
    dsimp [U]
    change B<s.re at hs
    linarith [Nat.cast_nonneg (α:=ℝ) M]
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt (hH M) hU,
    toMeromorphicNFAt_eq_self.mpr ha.meromorphicNFAt]
  exact hHF M hs

#print axioms glue
end QuantitativeArithmeticMeromorphicModels
