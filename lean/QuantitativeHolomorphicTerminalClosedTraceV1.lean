module

public import QuantitativeHolomorphicTerminalSourceTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic.Terminal

open Sharp
open ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCompactObservationCount AsymptoticFiniteBranch AsymptoticRegularTrace MeasureTheory
open AsymptoticCylinder AsymptoticCylinderModeComparison AsymptoticUnweightedKernel AsymptoticFourierNorm

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) {ι : Type*}

def sectorRegularTraceError (P : Parameters A) (h : ℕ) (Y H D : ℝ)
    (j J n d folds : ℕ) (E : Expression) : ℝ :=
  let P' := AsymptoticReconstructedCount.parameters A P
  let k : ℝ := 2*h+2
  let B : ℝ := (3/2:ℝ)^n
  (4*h+2 : ℝ)/k * (2+2*Sharp.countFilterMajorant A P n * majorantConstant (P'.s+4) (4*Real.pi) P'.ε) *
    Real.sqrt (countFilterError A P Y j J n d) +
  upperCutError (B^2*(1+majorantConstant (P'.s+4) (4*Real.pi) P'.ε)) B 1
    (massBound (2*h) (P'.s+4) (4*Real.pi) H/k) +
  (2*Real.sqrt (localizedErrorBound (P'.s+4) (4*Real.pi) Y)*
    Real.sqrt (massSlope (P'.s+4) (4*Real.pi) Y))*(Real.sqrt k)⁻¹ +
  (expressionBound E+(E.length:ℝ))*uniformRetainedTraceError D Y H h folds +
  countFilterError A P Y j J n d/(P'.ε*(4*Real.pi))

theorem finiteRetainedFilterTrace_source_comparison_of_replacement (hN : 0<N) (P : Parameters A)
    (h : ℕ) (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set UpperHalfPlane) (hs : ∀ i, IsCompact (s i))
    (Y H D : ℝ) (hY : 0<Y) (hH : 0<H) (hD : 0≤D) (j J n d : ℕ) (hJ : 0<J)
    (S : Finset ℤ) (hsmall : (h+1:ℝ)^(-(1/3:ℝ))*D≤1)
    (hfar : ∀ a : ℤ, a∉S → 2*compactBaseBound Y H 1≤1+|(a:ℝ)|)
    (E : Expression)
    (hp : ∀ m, holomorphicSum E m=holomorphicSum (countObservationFilterExpression A hN P e qs r s hs Y j J n d) m)
    (hr : ∀ z, regularSum E z=regularSum (countObservationFilterExpression A hN P e qs r s hs Y j J n d) z)
    (geom : ∀ b∈E, b.label≠1 → RetainedBranchGeometry b Y H D S) :
    let P' := AsymptoticReconstructedCount.parameters A P
    finiteRetainedFilterTrace A hN P h e qs r s hs Y H j J n d (P'.s+4)/(2*h+2:ℝ) -
      signedTrace volume (fun z => (regularSourceFilter A hN P e qs r s hs d z).comp
        (AsymptoticOrbitDiagonal.corner (AsymptoticCertificateOperators.highStrip P'.ε) z))/(4*Real.pi) ≤
      (2*Real.sqrt (localizedErrorBound (P'.s+4) (4*Real.pi) Y)*
        Real.sqrt (massSlope (P'.s+4) (4*Real.pi) Y))*(Real.sqrt (2*h+2:ℝ))⁻¹ +
      (expressionBound E+(E.length:ℝ))*uniformRetainedTraceError D Y H h S.card +
      countFilterError A P Y j J n d/(P'.ε*(4*Real.pi)) := by
  have ht := finiteRetainedFilterTrace_regular_comparison_of_replacement A hN P h e qs r s hs
    Y H D hY hH hD j J n d S hsmall hfar E hp hr geom
  have hsour := finiteRegularFilter_retained_trace_le_source A hN P e qs r s hs hY.le H j J n d hJ
  have he : regularRetained Y H (regularSum (countObservationFilterExpression A hN P e qs r s hs Y j J n d)) =
      fun z => (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z).comp
        ((observationRegularFilter A hN P e qs r s hs z
          (polynomialNormalizedReconstruction (scaledCutFiniteRegularCountReconstruction A hN P e z Y j J) n) d).comp
          (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z)) := by
    funext z
    simp only [regularRetained,regularSum_countObservationFilterExpression]
  rw [he] at hsour
  have hd := div_le_div_of_nonneg_right hsour (by positivity : 0≤4*Real.pi)
  rw [add_div,div_div] at hd
  have hab := (le_abs_self _).trans ht
  linarith only [hd,hab]

theorem sector_finrank_le_regular_source_trace_of_replacement (hN : 0 < N) (P : Parameters A)
    (h : ℕ) (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set UpperHalfPlane) (hs : ∀ i, IsCompact (s i))
    (Y H D : ℝ) (hY : 0 < Y) (hH : 0 < H) (hD : 0 ≤ D) (j J n d : ℕ) (hJ : 0 < J)
    (herr0 : 0 < countFilterError A P Y j J n d)
    (herr1 : countFilterError A P Y j J n d ≤ 1)
    (S : Finset ℤ) (hsmall : (h+1 : ℝ)^(-(1/3 : ℝ))*D ≤ 1)
    (hfar : ∀ a : ℤ, a ∉ S → 2*compactBaseBound Y H 1 ≤ 1+|(a:ℝ)|)
    (E : Expression)
    (hphysical : ∀ m, holomorphicSum E m = holomorphicSum (countObservationFilterExpression A hN P e qs r s hs Y j J n d) m)
    (hregular : ∀ z, regularSum E z = regularSum (countObservationFilterExpression A hN P e qs r s hs Y j J n d) z)
    (geom : ∀ b ∈ E,
      b.label ≠ 1 → RetainedBranchGeometry b Y H D S) :
    let P' := AsymptoticReconstructedCount.parameters A P
    (Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P'.s) e):ℝ)/(2*h+2:ℝ) ≤
      signedTrace volume (fun z => (regularSourceFilter A hN P e qs r s hs d z).comp
        (AsymptoticOrbitDiagonal.corner (AsymptoticCertificateOperators.highStrip P'.ε) z))/(4*Real.pi) +
      sectorRegularTraceError A P h Y H D j J n d S.card E := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let k : ℝ := 2*h+2
  let f := AsymptoticDiagonalTrace.trace
    (fourierBasis (2*h) (P'.s+4) (by positivity : 0 < 4*Real.pi) P'.epsilon_pos)
    (countObservationHolomorphicFilter A hN P h e qs r s hs
      (polynomialNormalizedReconstruction (scaledCutFiniteCountReconstruction A hN P h e Y j J) n) d)
  let v := finiteRetainedFilterTrace A hN P h e qs r s hs Y H j J n d (P'.s+4)
  let w := signedTrace volume (fun z => (regularSourceFilter A hN P e qs r s hs d z).comp
    (AsymptoticOrbitDiagonal.corner (AsymptoticCertificateOperators.highStrip P'.ε) z))/(4*Real.pi)
  let u := w
  let a := (2+2*Sharp.countFilterMajorant A P n*majorantConstant (P'.s+4) (4*Real.pi) P'.ε)*
    Real.sqrt (countFilterError A P Y j J n d)
  let b := upperCutError (((3/2:ℝ)^n)^2*(1+majorantConstant (P'.s+4) (4*Real.pi) P'.ε))
    ((3/2:ℝ)^n) 1 (massBound (2*h) (P'.s+4) (4*Real.pi) H/k)
  let c := (2*Real.sqrt (localizedErrorBound (P'.s+4) (4*Real.pi) Y)*
    Real.sqrt (massSlope (P'.s+4) (4*Real.pi) Y))*(Real.sqrt k)⁻¹ +
    (expressionBound E+(E.length:ℝ))*uniformRetainedTraceError D Y H h S.card +
    countFilterError A P Y j J n d/(P'.ε*(4*Real.pi))
  have hk : 0 < k := by dsimp [k]; positivity
  have hdim := Sharp.sector_finrank_le_finite_filter_trace A hN P h e qs r s hs Y hY.le j J n d hJ herr0 herr1
  have hd : (Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P'.s) e):ℝ)/k ≤
      f/k+(4*h+2:ℝ)/k*a := by
    have hh := div_le_div_of_nonneg_right hdim hk.le
    apply hh.trans_eq
    dsimp only [a]
    ring
  have ht := Sharp.finiteFilter_upperCut_explicit_error A hN P h e qs r s hs Y H hH j J n d
  have hfv : f/k-v/k ≤ b := by
    apply le_trans _ ht
    rw [← sub_div,Real.norm_eq_abs]
    exact div_le_div_of_nonneg_right (le_abs_self _) hk.le
  have hvu : v/k-u ≤ c :=
    finiteRetainedFilterTrace_source_comparison_of_replacement A hN P h e qs r s hs
      Y H D hY hH hD j J n d hJ S hsmall hfar E hphysical hregular geom
  have huw : u ≤ w := le_rfl
  change (Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P'.s) e):ℝ)/k ≤ w+_
  have he : sectorRegularTraceError A P h Y H D j J n d S.card E = (4*h+2:ℝ)/k*a+b+c := by
    dsimp [sectorRegularTraceError,a,b,c,k]
    ring
  rw [he]
  linarith


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

def closedSectorTraceError (hN : 0<N) (P : Parameters A) (h : ℕ)
    (qs : Finset ι) (r : ι → Row N) (L U Y H : ℝ) (j J n d folds : ℕ) : ℝ :=
  let D := quantifiedFilterMatrixHeight A hN qs r L U j J n d*(H+2)
  sectorRegularTraceError A P h Y H D j J n d folds [] +
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
  have ht := sector_finrank_le_regular_source_trace_quantified A hN P h e qs r s hs
    hL hre hlo hhi Y H hY hH j J n d hJ herr0 herr1 S hsmall hfar
  apply ht.trans
  apply add_le_add le_rfl
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
    (quantifiedFilterComplexity_le_closed A hN P e qs r L U Y j J n d)
    (uniformRetainedTraceError_nonneg _ H hY h S.card))

#print axioms sector_finrank_le_regular_source_trace_of_replacement
#print axioms sector_finrank_le_regular_source_trace_quantified
#print axioms sector_finrank_le_regular_source_trace_closed

end QuantitativeHolomorphic.Terminal
