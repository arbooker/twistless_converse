module

public import AsymptoticCylinderFiniteUpperCutoffV1
public import AsymptoticRegularFiniteUpperCutoffV1
public import AsymptoticFiniteTraceReductionV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticSharedApproximation

open UpperHalfPlane MeasureTheory Set Filter FinitenessCertificate FinitenessGlobalHeight
open AsymptoticSectorSigns AsymptoticReconstructedCount AsymptoticRegularTrace
open AsymptoticCompactObservationCount (Row)
open scoped Topology

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- Removing the upper cutoff in both realizations. The only remaining
premise is the finite-word trace limit with both height cutoffs fixed. -/
theorem finite_trace_limit_of_upper_cut_words (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (Y : ℝ) (n d : ℕ) (I : Finset ℤ) (e : Sector N)
    (hfinite : ∀ H : ℝ,0<H → Tendsto
      (fun h : ℕ => AsymptoticCylinderObservation.finiteUpperCutPolynomialTrace A hN P r s hs h e Y H n d I/(2*h+2:ℕ))
      atTop (𝓝 (AsymptoticRegularObservation.finiteUpperCutPolynomialTrace A hN P r s hs e Y H n d I/(4*Real.pi)))) :
    Tendsto
      (fun h : ℕ => AsymptoticCylinderObservation.finiteCutPolynomialTrace A hN P r s hs h e Y n d I/(2*h+2:ℕ))
      atTop (𝓝 (signedTrace volume
        (AsymptoticRegularObservation.finiteCutPolynomialTerminal A hN P r s hs e Y n d I)/(4*Real.pi))) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  have hδ3 : 0<δ/3 := by positivity
  obtain ⟨H₁,hH₁,hH⟩ := AsymptoticCylinderObservation.finiteUpperCutPolynomialTrace_approximation
    A hN P r s hs n hδ3
  obtain ⟨H₂,hH₂,hR⟩ := AsymptoticRegularObservation.finiteUpperCutPolynomialTrace_approximation
    A hN P r s hs n hδ3
  let H := max H₁ H₂
  have hHp : 0<H := hH₁.trans_le (le_max_left _ _)
  have hreg := hR H (le_max_right _ _) e Y d I
  let B := signedTrace volume (AsymptoticRegularObservation.finiteCutPolynomialTerminal A hN P r s hs e Y n d I)
  let T := AsymptoticRegularObservation.finiteUpperCutPolynomialTrace A hN P r s hs e Y H n d I
  have hπ : (1:ℝ)≤4*Real.pi := by nlinarith [Real.two_le_pi]
  have hπ0 : 0<4*Real.pi := by positivity
  have hBT : ‖T/(4*Real.pi)-B/(4*Real.pi)‖<δ/3 := by
    rw [← sub_div,norm_div,Real.norm_of_nonneg hπ0.le,norm_sub_rev]
    have hb : ‖B-T‖/(4*Real.pi)≤‖B-T‖ := by
      apply (div_le_iff₀ hπ0).mpr
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hπ (norm_nonneg (B-T))
    exact hb.trans_lt hreg
  have ht := (Metric.tendsto_nhds.mp (hfinite H hHp)) (δ/3) hδ3
  filter_upwards [ht,hH H (le_max_left _ _)] with h hh hc
  let F := AsymptoticCylinderObservation.finiteUpperCutPolynomialTrace A hN P r s hs h e Y H n d I/(2*h+2:ℕ)
  let U := AsymptoticCylinderObservation.finiteCutPolynomialTrace A hN P r s hs h e Y n d I/(2*h+2:ℕ)
  have hk : (0:ℝ)<(2*h+2:ℕ) := by positivity
  have hUF : ‖U-F‖<δ/3 := by
    simpa only [U,F,← sub_div,norm_div,Real.norm_of_nonneg hk.le] using hc e Y d I
  have hFT : ‖F-T/(4*Real.pi)‖<δ/3 := by simpa only [dist_eq_norm] using hh
  change dist U (B/(4*Real.pi))<δ
  rw [dist_eq_norm]
  have ha := norm_sub_le_norm_sub_add_norm_sub U F (B/(4*Real.pi))
  have hb := norm_sub_le_norm_sub_add_norm_sub F (T/(4*Real.pi)) (B/(4*Real.pi))
  linarith

/-- The actual uncut fixed-observation limit is reduced entirely to
finite polynomial words with fixed lower and upper cutoffs. No exact
upper-height identity block or sector dimension formula is assumed. -/
theorem holomorphic_trace_limit_of_upper_cut_words (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i))
    (hfinite : ∀ Y : ℝ,0<Y → Y≤(parameters A P).ε → ∀ H : ℝ,0<H →
      ∀ n d : ℕ,∀ I : Finset ℤ,∀ e : Sector N,
      Tendsto
        (fun h : ℕ => AsymptoticCylinderObservation.finiteUpperCutPolynomialTrace A hN P r s hs h e Y H n d I/(2*h+2:ℕ))
        atTop (𝓝 (AsymptoticRegularObservation.finiteUpperCutPolynomialTrace A hN P r s hs e Y H n d I/(4*Real.pi))))
    (e : Sector N) :
    Tendsto (fun h : ℕ => AsymptoticCylinderObservation.holomorphicTrace A hN P r s hs h e/(2*h+2:ℕ))
      atTop (𝓝 ((trace volume (AsymptoticRegularObservation.positive A hN P r s hs e)).toReal/(4*Real.pi))) := by
  apply holomorphic_trace_limit_of_finite_words A hN P r s hs _ e
  intro Y hY0 hY n d I e
  exact finite_trace_limit_of_upper_cut_words A hN P r s hs Y n d I e
    (fun H hH => hfinite Y hY0 hY H hH n d I e)

#print axioms finite_trace_limit_of_upper_cut_words
#print axioms holomorphic_trace_limit_of_upper_cut_words

end AsymptoticSharedApproximation
