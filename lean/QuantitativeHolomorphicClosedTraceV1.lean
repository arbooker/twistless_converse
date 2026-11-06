module

public import QuantitativeHolomorphicRawComplexityV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCompactObservationCount AsymptoticFiniteBranch AsymptoticRegularTrace
open MeasureTheory AsymptoticUnweightedKernel

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) {ι : Type*}

def closedFilterComplexity (hN : 0<N) (P : Parameters A)
    (qs : Finset ι) (r : ι → Row N) (L U : ℝ) (j J n d : ℕ) : ℝ :=
  let V := (4:ℝ)^(4^n)
  let K := rawReconstructionLength A j J*(3+(rawReconstructionLength A j J)^2)^(4^n)
  V^2*(1+∑ i∈qs,
    (quantifiedRowMass hN (r i) L U ((AsymptoticReconstructedCount.parameters A P).s+4)*V)^2)^d +
    ((K^2*(1+∑ i∈qs, (quantifiedRowLength hN (r i) L U*K)^2)^d : ℕ):ℝ)

theorem quantifiedFilterComplexity_le_closed (hN : 0<N) (P : Parameters A) (e : Sector N)
    (qs : Finset ι) (r : ι → Row N) (L U Y : ℝ) (j J n d : ℕ) :
    quantifiedFilterComplexity A hN P e qs r L U Y j J n d≤
      closedFilterComplexity A hN P qs r L U j J n d := by
  let R := scaledCutCountExpression A hN P e Y j J
  have hR := scaledCutCountExpression_mass_le_one A hN P e Y j J
  have hR0 := expressionBound_nonneg R
  change expressionBound R≤1 at hR
  have hp : (3+expressionBound R^2)^(4^n)≤(4:ℝ)^(4^n) := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [sq_nonneg (expressionBound R-1)]
  have hv : expressionBound R*(3+expressionBound R^2)^(4^n)≤(4:ℝ)^(4^n) :=
    (mul_le_mul hR hp (by positivity) zero_le_one).trans_eq (one_mul _)
  have hrows (i : ι) : 0≤quantifiedRowMass hN (r i) L U ((AsymptoticReconstructedCount.parameters A P).s+4) := by
    unfold quantifiedRowMass integerCompactDistortion
    positivity
  dsimp only [quantifiedFilterComplexity,closedFilterComplexity]
  rw [scaledCutCountExpression_length]
  apply add_le_add _ le_rfl
  gcongr
  all_goals first
    | exact hv
    | exact hrows _
    | exact mul_nonneg (hrows _) (mul_nonneg hR0 (pow_nonneg (by positivity) _))

def closedSectorTraceError (hN : 0<N) (P : Parameters A) (h : ℕ)
    (qs : Finset ι) (r : ι → Row N) (L U Y H : ℝ) (j J n d folds : ℕ) : ℝ :=
  let D := quantifiedFilterMatrixHeight A hN qs r L U j J n d*(H+2)
  Sharp.sectorRegularTraceError A P h Y H D j J n d folds [] +
    closedFilterComplexity A hN P qs r L U j J n d * uniformRetainedTraceError D Y H h folds

theorem sector_finrank_le_regular_source_trace_closed (hN : 0<N) (P : Parameters A)
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
      closedSectorTraceError A hN P h qs r L U Y H j J n d S.card := by
  have ht := Sharp.sector_finrank_le_regular_source_trace_quantified A hN P h e qs r s hs
    hL hre hlo hhi Y H hY hH j J n d hJ herr0 herr1 S hsmall hfar
  apply ht.trans
  apply add_le_add le_rfl
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
    (quantifiedFilterComplexity_le_closed A hN P e qs r L U Y j J n d)
    (uniformRetainedTraceError_nonneg _ H hY h S.card))

#print axioms quantifiedFilterComplexity_le_closed
#print axioms sector_finrank_le_regular_source_trace_closed

end QuantitativeHolomorphic
