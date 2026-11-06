module

public import QuantitativeHolomorphicReplacementTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCompactObservationCount AsymptoticFiniteBranch AsymptoticRegularTrace
open MeasureTheory AsymptoticUnweightedKernel

theorem uniformRetainedTraceError_nonneg (D H : ℝ) {Y : ℝ} (hY : 0<Y) (h folds : ℕ) :
    0 ≤ uniformRetainedTraceError D Y H h folds := by
  apply le_trans _ (le_max_left _ _)
  have hk := compactKernelBound_nonneg Y H 0
  unfold diagonalTraceError
  positivity

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) {ι : Type*}

/-- Explicit expansion cost for the complete counting filter: finite raw
reconstruction, Newton degree, number and size of rows, and filter degree.
No compactness-selected observation bound occurs. -/
def quantifiedFilterComplexity (hN : 0<N) (P : Parameters A) (e : Sector N)
    (qs : Finset ι) (r : ι → Row N) (L U Y : ℝ) (j J n d : ℕ) : ℝ :=
  let R := scaledCutCountExpression A hN P e Y j J
  let V := expressionBound R*(3+expressionBound R^2)^(4^n)
  let K := R.length*(3+R.length^2)^(4^n)
  V^2*(1+∑ i∈qs,
    (quantifiedRowMass hN (r i) L U ((AsymptoticReconstructedCount.parameters A P).s+4)*V)^2)^d +
    ((K^2*(1+∑ i∈qs, (quantifiedRowLength hN (r i) L U*K)^2)^d : ℕ):ℝ)

theorem quantifiedCountFilterExpression_total_complexity (hN : 0<N) (P : Parameters A) (e : Sector N)
    (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane) (hs : ∀ i, IsCompact (s i))
    {L U : ℝ} (hL : 0<L)
    (hre : ∀ i z, z∈s i → |z.re|≤1) (hlo : ∀ i z, z∈s i → L≤z.im)
    (hhi : ∀ i z, z∈s i → z.im≤U) (Y : ℝ) (j J n d : ℕ) :
    let E := quantifiedCountFilterExpression A hN P e qs r s hs hL hre hlo hhi Y j J n d
    expressionBound E+(E.length:ℝ) ≤ quantifiedFilterComplexity A hN P e qs r L U Y j J n d := by
  have hh := quantifiedCountFilterExpression_complexity A hN P e qs r s hs hL hre hlo hhi Y j J n d
  exact add_le_add hh.1 (by exact_mod_cast hh.2)

/-- All five trace-comparison losses, with actual constructed matrix
height and a closed expansion-cost bound instead of branch assumptions. -/
def quantifiedSectorTraceError (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N)
    (qs : Finset ι) (r : ι → Row N) (L U Y H : ℝ) (j J n d folds : ℕ) : ℝ :=
  let D := quantifiedFilterMatrixHeight A hN qs r L U j J n d*(H+2)
  sectorRegularTraceError A P h Y H D j J n d folds [] +
    quantifiedFilterComplexity A hN P e qs r L U Y j J n d * uniformRetainedTraceError D Y H h folds

/-- Global holomorphic sector-to-regular-source trace assembly for the
literal counting filter. The row replacements, their matrix geometry,
periodized nonreturn conditions, and all physical/regular identifications
are proved internally. The remaining assumptions are displayed numeric
cutoff inequalities and concrete region containment, not trace estimates. -/
theorem sector_finrank_le_regular_source_trace_quantified (hN : 0<N) (P : Parameters A)
    (h : ℕ) (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set UpperHalfPlane) (hs : ∀ i, IsCompact (s i))
    {L U : ℝ} (hL : 0<L)
    (hre : ∀ i z, z∈s i → |z.re|≤1) (hlo : ∀ i z, z∈s i → L≤z.im)
    (hhi : ∀ i z, z∈s i → z.im≤U)
    (Y H : ℝ) (hY : 0<Y) (hH : 0<H) (j J n d : ℕ) (hJ : 0<J)
    (herr0 : 0<countFilterError A P Y j J n d)
    (herr1 : countFilterError A P Y j J n d≤1)
    (S : Finset ℤ)
    (hsmall : (h+1:ℝ)^(-(1/3:ℝ)) *
      (quantifiedFilterMatrixHeight A hN qs r L U j J n d*(H+2))≤1)
    (hfar : ∀ a : ℤ, a ∉ S → 2*compactBaseBound Y H 1≤1+|(a:ℝ)|) :
    let P' := AsymptoticReconstructedCount.parameters A P
    (Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P'.s) e):ℝ)/(2*h+2:ℝ) ≤
      signedTrace volume (fun z => (regularSourceFilter A hN P e qs r s hs d z).comp
        (AsymptoticOrbitDiagonal.corner (AsymptoticCertificateOperators.highStrip P'.ε) z))/(4*Real.pi) +
      quantifiedSectorTraceError A hN P h e qs r L U Y H j J n d S.card := by
  let E := quantifiedCountFilterExpression A hN P e qs r s hs hL hre hlo hhi Y j J n d
  let B := quantifiedFilterMatrixHeight A hN qs r L U j J n d
  have hB := quantifiedFilterMatrixHeight_nonneg A hN qs r L U j J n d
  have hm := quantifiedCountFilterExpression_matrix_bound A hN P e qs r s hs hL hre hlo hhi Y j J n d
  have ht := sector_finrank_le_regular_source_trace_of_replacement A hN P h e qs r s hs
    Y H (B*(H+2)) hY hH (by positivity) j J n d hJ herr0 herr1 S hsmall hfar E
    (quantifiedCountFilterExpression_physical A hN P e qs r s hs hL hre hlo hhi Y j J n d)
    (quantifiedCountFilterExpression_regular A hN P e qs r s hs hL hre hlo hhi Y j J n d)
    (fun b hb hne => hm.geometry hB Y H S b hb hne)
  apply ht.trans
  apply add_le_add le_rfl
  have hc := quantifiedCountFilterExpression_total_complexity A hN P e qs r s hs hL hre hlo hhi Y j J n d
  have hn := uniformRetainedTraceError_nonneg (B*(H+2)) H hY h S.card
  have hb := mul_le_mul_of_nonneg_right hc hn
  change sectorRegularTraceError A P h Y H (B*(H+2)) j J n d S.card E ≤
    sectorRegularTraceError A P h Y H (B*(H+2)) j J n d S.card [] +
      quantifiedFilterComplexity A hN P e qs r L U Y j J n d *
        uniformRetainedTraceError (B*(H+2)) Y H h S.card
  simp only [sectorRegularTraceError, show expressionBound ([]:Expression)=0 from rfl,
    List.length_nil, Nat.cast_zero, add_zero, zero_mul]
  change (expressionBound E+(E.length:ℝ))*uniformRetainedTraceError (B*(H+2)) Y H h S.card ≤ _ at hb
  linarith only [hb]

#print axioms quantifiedCountFilterExpression_total_complexity
#print axioms sector_finrank_le_regular_source_trace_quantified

end QuantitativeHolomorphic
