module
public import QuantitativeArithmeticCurvedTaylorContinuationV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticCurvedTaylor
open Complex Filter Set MeasureTheory SmallLevelTaylor SmallLevelAdditive
open FinitenessPolynomialSeries
open scoped Topology

theorem continued_sum_weight_order (k : ℕ) {c : ℝ} (hc : 0<c) (r : ℝ)
    (G : ℂ → ℂ) (hG : ∀ s, MeromorphicAt G s)
    (hGa : ∀ s, s≠(k:ℂ) → AnalyticAt ℂ G s)
    (hGo : (-1:WithTop ℤ)≤meromorphicOrderAt G (k:ℂ)) (M : ℕ) :
    (-1:WithTop ℤ)≤meromorphicOrderAt
      (fun z => ∑ n∈Finset.range M, continuedTerm k c r G n z) (k:ℂ) := by
  have hneg : (-1:WithTop ℤ)≤0 := by decide
  have ht (n : ℕ) : (-1:WithTop ℤ)≤meromorphicOrderAt (continuedTerm k c r G n) (k:ℂ) := by
    let A : ℂ → ℂ := fun z => (I/(r:ℂ))^n*(c:ℂ)^(z+(n:ℂ))*
      Ring.choose (z+(n:ℂ)-(k:ℂ)) n
    let V : ℂ → ℂ := fun z => G (z+(n:ℂ))
    have hA : AnalyticAt ℂ A (k:ℂ) :=
      (term_scalar_analytic hc r n (k:ℂ)).mul (binomial_shift_analytic k n (k:ℂ))
    have hV : MeromorphicAt V (k:ℂ) :=
      (hG ((k:ℂ)+n)).comp_analyticAt (g:=fun z : ℂ => z+n)
        (analyticAt_id.add analyticAt_const)
    have hVo : (-1:WithTop ℤ)≤meromorphicOrderAt V (k:ℂ) := by
      dsimp only [V]
      rw [meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt]
      by_cases hn : n=0
      · simpa only [hn,Nat.cast_zero,add_zero] using hGo
      · have hk : (k:ℂ)+(n:ℂ)≠(k:ℂ) := by
          intro hh
          have hz : (n:ℂ)=0 := add_left_cancel (hh.trans (add_zero (k:ℂ)).symm)
          exact hn (Nat.cast_eq_zero.mp hz)
        exact le_trans hneg (hGa _ hk).meromorphicOrderAt_nonneg
    have he : continuedTerm k c r G n=A*V := by
      funext z
      simp only [continuedTerm,A,V,Pi.mul_apply,mul_assoc]
    rw [he,meromorphicOrderAt_mul hA.meromorphicAt hV]
    have hh := add_le_add hA.meromorphicOrderAt_nonneg hVo
    simpa only [zero_add] using hh
  induction M with
  | zero =>
    simp only [Finset.range_zero,Finset.sum_empty]
    exact hneg.trans (analyticAt_const (v := (0:ℂ))).meromorphicOrderAt_nonneg
  | succ M ih =>
    have hm : MeromorphicAt (fun z => ∑ n∈Finset.range M, continuedTerm k c r G n z) (k:ℂ) :=
      MeromorphicAt.fun_sum (fun n _ => continuedTerm_meromorphic k hc r G hG n (k:ℂ))
    have hh := (le_min ih (ht M)).trans
      (meromorphicOrderAt_add hm (continuedTerm_meromorphic k hc r G hG M (k:ℂ)))
    have he : (fun z => ∑ n∈Finset.range (M+1), continuedTerm k c r G n z)=
        (fun z => ∑ n∈Finset.range M, continuedTerm k c r G n z)+continuedTerm k c r G M := by
      funext z
      exact Finset.sum_range_succ _ _
    rw [he]
    exact hh

/-- The remaining weight pole of the curved transform is still at most simple. -/
theorem weight_pole_bound (k : ℕ) {a : ℕ → ℂ} (ha : PolynomialBound a)
    (ha0 : a 0=0) {c : ℝ} (hc : 0<c) (β r T : ℝ) (hr : r≠0) (hT : 0<T)
    (BG : ℝ) (G : ℂ → ℂ) (hG : ∀ s, MeromorphicAt G s)
    (hGa : ∀ s, s≠(k:ℂ) → AnalyticAt ℂ G s)
    (hGo : (-1:WithTop ℤ)≤meromorphicOrderAt G (k:ℂ))
    (hGF : ∀ s, BG<s.re → G s=transform a β s)
    (BJ : ℝ) (J : ℂ → ℂ) (hJ : ∀ s, MeromorphicNFAt J s)
    (hJF : ∀ s, BJ<s.re → J s=mellin (truncated k a β c r T) s) :
    (-1:WithTop ℤ)≤meromorphicOrderAt J (k:ℂ) := by
  obtain ⟨B,hB⟩ := continued_models k ha ha0 hc β r T hr hT BG G hG hGF
  obtain ⟨K,hK⟩ := all_mellin_models k ha ha0 hc β r T hr hT
  obtain ⟨M,hM⟩ := exists_nat_gt (max B K-(k:ℝ))
  have hBs : B-(M:ℝ)<(k:ℂ).re := by
    simp only [Complex.natCast_re]
    linarith [le_max_left B K]
  have hKs : K-(M:ℝ)<(k:ℂ).re := by
    simp only [Complex.natCast_re]
    linarith [le_max_right B K]
  let H : ℂ → ℂ := fun z => mellin (remainder k a β c r T M) z+
    ∑ n∈Finset.range M, continuedTerm k c r G n z
  have he : J=ᶠ[𝓝[≠] (k:ℂ)] H := by
    apply SmallLevelContinuation.halfplane_germ_identity (B-(M:ℝ)) (max BJ B)
    · exact fun z _ => (hJ z).meromorphicAt
    · exact fun z hz => (hB M).1 z hz
    · intro z hz
      exact (hJF z (lt_of_le_of_lt (le_max_left _ _) hz)).trans
        ((hB M).2 z (lt_of_le_of_lt (le_max_right _ _) hz)).symm
    · exact hBs
  rw [meromorphicOrderAt_congr he]
  have hR := (hK M).1 (k:ℂ) hKs
  have hm : MeromorphicAt (fun z => ∑ n∈Finset.range M, continuedTerm k c r G n z) (k:ℂ) :=
    MeromorphicAt.fun_sum (fun n _ => continuedTerm_meromorphic k hc r G hG n (k:ℂ))
  have hneg : (-1:WithTop ℤ)≤0 := by decide
  exact (le_min (le_trans hneg hR.meromorphicOrderAt_nonneg)
    (continued_sum_weight_order k hc r G hG hGa hGo M)).trans
      (meromorphicOrderAt_add hR.meromorphicAt hm)

#print axioms continued_sum_weight_order
#print axioms weight_pole_bound
end QuantitativeArithmeticCurvedTaylor
