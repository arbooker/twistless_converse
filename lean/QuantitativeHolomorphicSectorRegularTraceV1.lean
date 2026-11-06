module

public import QuantitativeHolomorphicRegularSourceTraceV1
public import QuantitativeHolomorphicFilterCutoffV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCompactObservationCount AsymptoticFiniteBranch AsymptoticRegularTrace MeasureTheory
open AsymptoticCylinder AsymptoticCylinderModeComparison AsymptoticUnweightedKernel AsymptoticFourierNorm

variable {N Q : ℕ} {hQ : 0 < Q} (A : Certificate N Q hQ)
variable {ι : Type*}

/-- The five explicit errors in the actual sector-to-regular comparison:
normalization, upper cusp, weighted projection, finite rational branches, and
finite-to-exact regular normalization. -/
def sectorRegularTraceError (P : Parameters A) (h : ℕ) (Y H D : ℝ)
    (j J n d folds : ℕ) (E : Expression) : ℝ :=
  let P' := AsymptoticReconstructedCount.parameters A P
  let k : ℝ := 2*h+2
  let B : ℝ := 4^(4^n)
  (4*h+2 : ℝ)/k * (2+2*countFilterMajorant A P n * majorantConstant (P'.s+4) (4*Real.pi) P'.ε) *
    Real.sqrt (countFilterError A P Y j J n d) +
  upperCutError (B^2*(1+majorantConstant (P'.s+4) (4*Real.pi) P'.ε)) B 1
    (massBound (2*h) (P'.s+4) (4*Real.pi) H/k) +
  (2*Real.sqrt (localizedErrorBound (P'.s+4) (4*Real.pi) Y)*
    Real.sqrt (massSlope (P'.s+4) (4*Real.pi) Y))*(Real.sqrt k)⁻¹ +
  (expressionBound E+(E.length:ℝ))*uniformRetainedTraceError D Y H h folds +
  countFilterError A P Y j J n d/(Y*(4*Real.pi))

/-- Literal sector finrank versus the actual terminal regular polynomial
filter, with all physical-to-regular losses explicit. The displayed branch
geometry is the remaining certificate input; no trace comparison, regularity,
sector-fixing, or summability conclusion is assumed. -/
theorem sector_finrank_le_regular_source_trace (hN : 0 < N) (P : Parameters A)
    (h : ℕ) (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set UpperHalfPlane) (hs : ∀ i, IsCompact (s i))
    (Y H D : ℝ) (hY : 0 < Y) (hH : 0 < H) (hD : 0 ≤ D) (j J n d : ℕ) (hJ : 0 < J)
    (herr0 : 0 < countFilterError A P Y j J n d)
    (herr1 : countFilterError A P Y j J n d ≤ 1)
    (S : Finset ℤ) (hsmall : (h+1 : ℝ)^(-(1/3 : ℝ))*D ≤ 1)
    (hfar : ∀ a : ℤ, a ∉ S → 2*compactBaseBound Y H 1 ≤ 1+|(a:ℝ)|)
    (geom : ∀ b ∈ countObservationFilterExpression A hN P e qs r s hs Y j J n d,
      b.label ≠ 1 → RetainedBranchGeometry b Y H D S) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let E := countObservationFilterExpression A hN P e qs r s hs Y j J n d
    (Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P'.s) e):ℝ)/(2*h+2:ℝ) ≤
      signedTrace volume (fun z => (regularSourceFilter A hN P e qs r s hs d z).comp
        (AsymptoticOrbitDiagonal.corner (AsymptoticCertificateOperators.highStrip P'.ε) z))/(4*Real.pi) +
      sectorRegularTraceError A P h Y H D j J n d S.card E := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let E := countObservationFilterExpression A hN P e qs r s hs Y j J n d
  let k : ℝ := 2*h+2
  let f := AsymptoticDiagonalTrace.trace
    (fourierBasis (2*h) (P'.s+4) (by positivity : 0 < 4*Real.pi) P'.epsilon_pos)
    (countObservationHolomorphicFilter A hN P h e qs r s hs
      (polynomialNormalizedReconstruction (scaledCutFiniteCountReconstruction A hN P h e Y j J) n) d)
  let v := finiteRetainedFilterTrace A hN P h e qs r s hs Y H j J n d (P'.s+4)
  let B := fun z => observationRegularFilter A hN P e qs r s hs z
    (normalizedReconstruction (scaledRegularCountReconstruction A hN P e z)) d
  let u := signedTrace volume (regularRetained Y H B)/(4*Real.pi)
  let w := signedTrace volume (fun z => (regularSourceFilter A hN P e qs r s hs d z).comp
    (AsymptoticOrbitDiagonal.corner (AsymptoticCertificateOperators.highStrip P'.ε) z))/(4*Real.pi)
  let a := (2+2*countFilterMajorant A P n*majorantConstant (P'.s+4) (4*Real.pi) P'.ε)*
    Real.sqrt (countFilterError A P Y j J n d)
  let b := upperCutError (((4:ℝ)^(4^n))^2*(1+majorantConstant (P'.s+4) (4*Real.pi) P'.ε))
    ((4:ℝ)^(4^n)) 1 (massBound (2*h) (P'.s+4) (4*Real.pi) H/k)
  let c := (2*Real.sqrt (localizedErrorBound (P'.s+4) (4*Real.pi) Y)*
    Real.sqrt (massSlope (P'.s+4) (4*Real.pi) Y))*(Real.sqrt k)⁻¹ +
    (expressionBound E+(E.length:ℝ))*uniformRetainedTraceError D Y H h S.card +
    countFilterError A P Y j J n d/(Y*(4*Real.pi))
  have hk : 0 < k := by dsimp [k]; positivity
  have hdim := sector_finrank_le_finite_filter_trace A hN P h e qs r s hs Y hY.le j J n d hJ herr0 herr1
  have hd : (Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P'.s) e):ℝ)/k ≤
      f/k+(4*h+2:ℝ)/k*a := by
    have hh := div_le_div_of_nonneg_right hdim hk.le
    apply hh.trans_eq
    dsimp only [a]
    ring
  have ht := finiteFilter_upperCut_explicit_error A hN P h e qs r s hs Y H hH j J n d
  have hfv : f/k-v/k ≤ b := by
    apply le_trans _ ht
    rw [← sub_div,Real.norm_eq_abs]
    exact div_le_div_of_nonneg_right (le_abs_self _) hk.le
  have hvu : v/k-u ≤ c := (le_abs_self _).trans
    (finiteRetainedFilterTrace_exact_regular_comparison A hN P h e qs r s hs
      Y H D hY hH hD j J n d hJ S hsmall hfar geom)
  have huw : u ≤ w := div_le_div_of_nonneg_right
    (observationRegularFilter_retained_trace_le_source A hN P e qs r s hs d Y H)
    (by positivity : 0 ≤ 4*Real.pi)
  change (Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P'.s) e):ℝ)/k ≤ w+_
  have he : sectorRegularTraceError A P h Y H D j J n d S.card E = (4*h+2:ℝ)/k*a+b+c := by
    dsimp [sectorRegularTraceError,a,b,c,k]
    ring
  rw [he]
  linarith

#print axioms sector_finrank_le_regular_source_trace

end QuantitativeHolomorphic
