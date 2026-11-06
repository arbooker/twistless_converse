module
public import QuantitativeArithmeticCurvedTaylorModelsV1
public import QuantitativeArithmeticMeromorphicHalfplaneModelsV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticCurvedTaylor
open Complex Filter Set MeasureTheory SmallLevelTaylor SmallLevelAdditive
open FinitenessPolynomialSeries
open scoped Topology

/-- A meromorphic additive Mellin transform continues the actual truncated
curved transform. -/
theorem meromorphic_continuation (k : ℕ) {a : ℕ → ℂ} (ha : PolynomialBound a)
    (ha0 : a 0=0) {c : ℝ} (hc : 0<c) (β r T : ℝ) (hr : r≠0) (hT : 0<T)
    (BG : ℝ) (G : ℂ → ℂ) (hG : ∀ s, MeromorphicAt G s)
    (hGF : ∀ s, BG<s.re → G s=transform a β s) :
    ∃ (B : ℝ) (J : ℂ → ℂ), (∀ s, MeromorphicNFAt J s) ∧
      ∀ s, B<s.re → J s=mellin (truncated k a β c r T) s := by
  obtain ⟨B,hB⟩ := continued_models k ha ha0 hc β r T hr hT BG G hG hGF
  obtain ⟨K,hK⟩ := all_mellin_models k ha ha0 hc β r T hr hT
  let C := max B K
  let H : ℕ → ℂ → ℂ := fun M s => mellin (remainder k a β c r T M) s+
    ∑ n∈Finset.range M, continuedTerm k c r G n s
  have haF : AnalyticOnNhd ℂ (mellin (truncated k a β c r T)) {s : ℂ | C<s.re} := by
    intro s hs
    have hh := (hK 0).1 s (by
      simpa only [Set.mem_ofPred_eq,Nat.cast_zero,sub_zero] using
        lt_of_le_of_lt (le_max_right B K) hs)
    have he : remainder k a β c r T 0=truncated k a β c r T := by
      funext y
      simp [remainder,polynomial]
    rwa [he] at hh
  have hm : ∀ M : ℕ, MeromorphicOn (H M) {s : ℂ | C-(M:ℝ)<s.re} := by
    intro M s hs
    apply (hB M).1 s
    change C-(M:ℝ)<s.re at hs
    change B-(M:ℝ)<s.re
    dsimp [C] at hs
    linarith [le_max_left B K]
  have he : ∀ M : ℕ, EqOn (H M) (mellin (truncated k a β c r T)) {s : ℂ | C<s.re} := by
    intro M s hs
    exact (hB M).2 s (lt_of_le_of_lt (le_max_left B K) hs)
  obtain ⟨J,hJ,hJF⟩ := QuantitativeArithmeticMeromorphicModels.glue C _ H haF hm he
  exact ⟨C,J,hJ,fun s hs => hJF hs⟩

/-- Curving the ray introduces no poles away from the weight when the
underlying additive transform has only a possible simple weight pole. -/
theorem analytic_away_weight (k : ℕ) {a : ℕ → ℂ} (ha : PolynomialBound a)
    (ha0 : a 0=0) {c : ℝ} (hc : 0<c) (β r T : ℝ) (hr : r≠0) (hT : 0<T)
    (BG : ℝ) (G : ℂ → ℂ) (hG : ∀ s, MeromorphicAt G s)
    (hGa : ∀ s, s≠(k:ℂ) → AnalyticAt ℂ G s)
    (hGo : (-1:WithTop ℤ)≤meromorphicOrderAt G (k:ℂ))
    (hGF : ∀ s, BG<s.re → G s=transform a β s)
    (BJ : ℝ) (J : ℂ → ℂ) (hJ : ∀ s, MeromorphicNFAt J s)
    (hJF : ∀ s, BJ<s.re → J s=mellin (truncated k a β c r T) s)
    (s : ℂ) (hs : s≠(k:ℂ)) : AnalyticAt ℂ J s := by
  obtain ⟨B,hB⟩ := continued_models k ha ha0 hc β r T hr hT BG G hG hGF
  obtain ⟨K,hK⟩ := all_mellin_models k ha ha0 hc β r T hr hT
  obtain ⟨M,hM⟩ := exists_nat_gt (max B K-s.re)
  have hBs : B-(M:ℝ)<s.re := by linarith [le_max_left B K]
  have hKs : K-(M:ℝ)<s.re := by linarith [le_max_right B K]
  obtain ⟨R,hR,he⟩ := continued_sum_extension k hc r G hG hGa hGo M s hs
  let H : ℂ → ℂ := fun z => mellin (remainder k a β c r T M) z+
    ∑ n∈Finset.range M, continuedTerm k c r G n z
  let U : ℂ → ℂ := fun z => mellin (remainder k a β c r T M) z+R z
  have hU : AnalyticAt ℂ U s := ((hK M).1 s hKs).add hR
  have hHU : H=ᶠ[𝓝[≠] s] U := by
    filter_upwards [he] with z hz
    dsimp only [H,U]
    rw [hz]
  exact SmallLevelSimplePoleTaylor.analyticAt_of_model _ J H U BJ B (B-(M:ℝ)) s
    hJ hJF (fun z hz => (hB M).1 z hz) ((hB M).2) hBs hU hHU

#print axioms meromorphic_continuation
#print axioms analytic_away_weight
end QuantitativeArithmeticCurvedTaylor
