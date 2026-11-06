module
public import QuantitativeArithmeticCurvedTaylorMellinV1
public import SmallLevelSimplePoleTaylorTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticCurvedTaylor
open Complex Filter Set MeasureTheory SmallLevelTaylor SmallLevelAdditive
open FinitenessPolynomialSeries
open scoped Topology

def continuedTerm (k : ℕ) (c r : ℝ) (G : ℂ → ℂ) (n : ℕ) (s : ℂ) : ℂ :=
  (I/(r:ℂ))^n*(c:ℂ)^(s+(n:ℂ))*(Ring.choose (s+(n:ℂ)-(k:ℂ)) n*G (s+n))

theorem term_scalar_analytic {c : ℝ} (hc : 0<c) (r : ℝ) (n : ℕ) (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => (I/(r:ℂ))^n*(c:ℂ)^(z+(n:ℂ))) s := by
  simp_rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hc.ne')]
  fun_prop

theorem continuedTerm_meromorphic (k : ℕ) {c : ℝ} (hc : 0<c) (r : ℝ)
    (G : ℂ → ℂ) (hG : ∀ s, MeromorphicAt G s) (n : ℕ) (s : ℂ) :
    MeromorphicAt (continuedTerm k c r G n) s := by
  exact (term_scalar_analytic hc r n s).meromorphicAt.mul
    ((binomial_shift_analytic k n s).meromorphicAt.mul
      ((hG (s+n)).comp_analyticAt (g:=fun z : ℂ => z+n)
        (analyticAt_id.add analyticAt_const)))

/-- Meromorphic Taylor models for the actual curved Mellin integral. No
functional equation for the curved ray is an input. -/
theorem continued_models (k : ℕ) {a : ℕ → ℂ} (ha : PolynomialBound a)
    (ha0 : a 0=0) {c : ℝ} (hc : 0<c) (β r T : ℝ) (hr : r≠0) (hT : 0<T)
    (BG : ℝ) (G : ℂ → ℂ) (hG : ∀ s, MeromorphicAt G s)
    (hGF : ∀ s, BG<s.re → G s=transform a β s) :
    ∃ B : ℝ, ∀ M : ℕ,
      MeromorphicOn (fun s => mellin (remainder k a β c r T M) s+
        ∑ n∈Finset.range M, continuedTerm k c r G n s) {s : ℂ | B-(M:ℝ)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        mellin (remainder k a β c r T M) s+
          ∑ n∈Finset.range M, continuedTerm k c r G n s=
            mellin (truncated k a β c r T) s := by
  obtain ⟨B,hB⟩ := all_mellin_models k ha ha0 hc β r T hr hT
  refine ⟨max B BG,fun M => ⟨?_,?_⟩⟩
  · intro s hs
    have hb : B-(M:ℝ)<s.re := by
      change max B BG-(M:ℝ)<s.re at hs
      linarith [le_max_left B BG]
    exact ((hB M).1 s hb).meromorphicAt.add
      (MeromorphicAt.fun_sum (fun n _ => continuedTerm_meromorphic k hc r G hG n s))
  · intro s hs
    rw [(hB M).2 s (lt_of_le_of_lt (le_max_left _ _) hs)]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    have hgn : BG<(s+(n:ℂ)).re := by
      simp only [Complex.add_re,Complex.natCast_re]
      have hh := lt_of_le_of_lt (le_max_right B BG) hs
      linarith [Nat.cast_nonneg (α:=ℝ) n]
    unfold continuedTerm mellinTaylorTerm
    rw [hGF _ hgn]
    ring

/-- Away from the weight, the possible shifted weight poles cancel against
Taylor coefficients, including at points k-n. -/
theorem continued_sum_extension (k : ℕ) {c : ℝ} (hc : 0<c) (r : ℝ)
    (G : ℂ → ℂ) (hG : ∀ s, MeromorphicAt G s)
    (hGa : ∀ s, s≠(k:ℂ) → AnalyticAt ℂ G s)
    (hGo : (-1:WithTop ℤ)≤meromorphicOrderAt G (k:ℂ))
    (M : ℕ) (s : ℂ) (hs : s≠(k:ℂ)) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R s ∧
      (fun z => ∑ n∈Finset.range M, continuedTerm k c r G n z)=ᶠ[𝓝[≠] s] R := by
  induction M with
  | zero =>
    refine ⟨fun _ => 0,analyticAt_const,?_⟩
    filter_upwards with z
    simp
  | succ M ih =>
    obtain ⟨R,hR,he⟩ := ih
    obtain ⟨U,hU,hu⟩ := SmallLevelSimplePoleTaylor.term_extension k M G hG hGa hGo s hs
    refine ⟨fun z => R z+(I/(r:ℂ))^M*(c:ℂ)^(z+(M:ℂ))*U z,
      hR.add ((term_scalar_analytic hc r M s).mul hU),?_⟩
    filter_upwards [he,hu] with z hz hzu
    rw [Finset.sum_range_succ,hz]
    dsimp only [continuedTerm]
    rw [hzu]

#print axioms continued_models
#print axioms continued_sum_extension
end QuantitativeArithmeticCurvedTaylor
