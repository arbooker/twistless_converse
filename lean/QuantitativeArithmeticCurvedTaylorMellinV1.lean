module
public import QuantitativeArithmeticCurvedTaylorRemainderV1
public import SmallLevelTaylorMellinRowsV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticCurvedTaylor
open Complex Filter Set MeasureTheory Asymptotics SmallLevelTaylor
open FinitenessPolynomialSeries
open scoped Topology

theorem truncated_convergent (k : ℕ) {a : ℕ → ℂ} (ha : PolynomialBound a)
    (ha0 : a 0=0) {c : ℝ} (hc : 0<c) :
    ∃ K : ℕ, ∀ β r T : ℝ, r≠0 → 0<T → ∀ s : ℂ, (K:ℝ)<s.re →
      MellinConvergent (truncated k a β c r T) s := by
  obtain ⟨K,hK⟩ := remainder_small k ha ha0 hc
  refine ⟨K,fun β r T hr hT s hs => ?_⟩
  have he : remainder k a β c r T 0=truncated k a β c r T := by
    funext y
    simp [remainder,polynomial]
  have hh := mellinConvergent_of_isBigO_rpow
    (remainder_locallyIntegrable k ha β r T hc 0)
    (remainder_rapid k ha ha0 β r T hc 0 (-(s.re+1))) (lt_add_one s.re)
    (by simpa only [Nat.cast_zero,zero_sub] using hK β r T hr hT 0) hs
  rwa [he] at hh

theorem polynomial_convergent (k : ℕ) {a : ℕ → ℂ} (ha : PolynomialBound a)
    (ha0 : a 0=0) {c : ℝ} (hc : 0<c) :
    ∃ K : ℕ, ∀ β r : ℝ, ∀ s : ℂ, (K:ℝ)<s.re → ∀ M : ℕ,
      MellinConvergent (polynomial k a β c r M) s := by
  obtain ⟨K,hK⟩ := taylorTerm_convergent k ha ha0 hc
  refine ⟨K,fun β r s hs M => ?_⟩
  unfold MellinConvergent
  simp only [polynomial,Finset.smul_sum]
  exact integrable_finsetSum (Finset.range M) (fun n _ => hK β r s hs n)

theorem polynomial_mellin (k : ℕ) {a : ℕ → ℂ} (ha : PolynomialBound a)
    (ha0 : a 0=0) {c : ℝ} (hc : 0<c) :
    ∃ B : ℝ, ∀ β r : ℝ, ∀ s : ℂ, B<s.re → ∀ M : ℕ,
      mellin (polynomial k a β c r M) s=
        ∑ n∈Finset.range M, mellinTaylorTerm k a β c r n s := by
  obtain ⟨K,hK⟩ := taylorTerm_convergent k ha ha0 hc
  obtain ⟨B,hB⟩ := taylorTerm_additive_mellin k ha ha0 hc
  refine ⟨max (K:ℝ) B,fun β r s hs M => ?_⟩
  have he : mellin (polynomial k a β c r M) s=
      ∑ n∈Finset.range M, mellin (taylorTerm k a β c r n) s := by
    unfold mellin
    simp only [polynomial,Finset.smul_sum]
    exact integral_finsetSum (Finset.range M)
      (fun n _ => hK β r s (lt_of_le_of_lt (le_max_left _ _) hs) n)
  rw [he]
  apply Finset.sum_congr rfl
  intro n hn
  exact hB β r s (lt_of_le_of_lt (le_max_right _ _) hs) n

/-- Actual Mellin identities for a truncated curved Fourier ray, at every
Taylor order and on one common initial half-plane. -/
theorem all_mellin_models (k : ℕ) {a : ℕ → ℂ} (ha : PolynomialBound a)
    (ha0 : a 0=0) {c : ℝ} (hc : 0<c) (β r T : ℝ) (hr : r≠0) (hT : 0<T) :
    ∃ B : ℝ, ∀ M : ℕ,
      AnalyticOnNhd ℂ (mellin (remainder k a β c r T M)) {s : ℂ | B-(M:ℝ)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        mellin (truncated k a β c r T) s=
          mellin (remainder k a β c r T M) s+
            ∑ n∈Finset.range M, mellinTaylorTerm k a β c r n s := by
  obtain ⟨K,hK⟩ := remainder_mellin_analytic k ha ha0 hc
  obtain ⟨C,hC⟩ := truncated_convergent k ha ha0 hc
  obtain ⟨D,hD⟩ := polynomial_convergent k ha ha0 hc
  obtain ⟨E,hE⟩ := polynomial_mellin k ha ha0 hc
  let B : ℝ := max (max (K:ℝ) (C:ℝ)) (max (D:ℝ) E)
  have hBK : (K:ℝ)≤B := (le_max_left _ _).trans (le_max_left _ _)
  have hBC : (C:ℝ)≤B := (le_max_right _ _).trans (le_max_left _ _)
  have hBD : (D:ℝ)≤B := (le_max_left _ _).trans (le_max_right _ _)
  have hBE : E≤B := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨B,fun M => ⟨?_,?_⟩⟩
  · intro s hs
    change B-(M:ℝ)<s.re at hs
    exact hK β r T hr hT M s (by change (K:ℝ)-(M:ℝ)<s.re; linarith)
  · intro s hs
    have hh := (hasMellin_sub (hC β r T hr hT s (hBC.trans_lt hs))
      (hD β r s (hBD.trans_lt hs) M)).2
    change mellin (remainder k a β c r T M) s=
      mellin (truncated k a β c r T) s-mellin (polynomial k a β c r M) s at hh
    rw [hE β r s (hBE.trans_lt hs) M] at hh
    linear_combination -hh

#print axioms all_mellin_models
end QuantitativeArithmeticCurvedTaylor
