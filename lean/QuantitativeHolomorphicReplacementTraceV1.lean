module

public import QuantitativeHolomorphicQuantifiedComplexityV1
public import QuantitativeHolomorphicSectorRegularTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCompactObservationCount AsymptoticFiniteBranch AsymptoticRegularTrace MeasureTheory
open AsymptoticCylinder AsymptoticCylinderModeComparison AsymptoticUnweightedKernel AsymptoticFourierNorm
open AsymptoticObservation

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) {ι : Type*}

theorem finiteRetainedFilterTrace_regular_comparison_of_replacement (hN : 0 < N) (P : Parameters A)
    (h : ℕ) (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set UpperHalfPlane) (hs : ∀ i, IsCompact (s i))
    (Y H D : ℝ) (hY : 0 < Y) (hH : 0 < H) (hD : 0 ≤ D) (j J n d : ℕ)
    (S : Finset ℤ) (hsmall : (h+1 : ℝ)^(-(1/3 : ℝ))*D ≤ 1)
    (hfar : ∀ a : ℤ, a ∉ S → 2 * compactBaseBound Y H 1 ≤ 1 + |(a : ℝ)|)
    (E : Expression)
    (hphysical : ∀ m, holomorphicSum E m = holomorphicSum (countObservationFilterExpression A hN P e qs r s hs Y j J n d) m)
    (hregular : ∀ z, regularSum E z = regularSum (countObservationFilterExpression A hN P e qs r s hs Y j J n d) z)
    (geom : ∀ b ∈ E,
      b.label ≠ 1 → RetainedBranchGeometry b Y H D S) :
    let P' := AsymptoticReconstructedCount.parameters A P
    |finiteRetainedFilterTrace A hN P h e qs r s hs Y H j J n d (P'.s+4) / (2*h+2 : ℝ) -
      signedTrace volume (fun z => (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z).comp
        ((observationRegularFilter A hN P e qs r s hs z
          (polynomialNormalizedReconstruction (scaledCutFiniteRegularCountReconstruction A hN P e z Y j J) n) d).comp
          (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z))) / (4*Real.pi)| ≤
      (2 * Real.sqrt (localizedErrorBound (P'.s+4) (4*Real.pi) Y) *
        Real.sqrt (massSlope (P'.s+4) (4*Real.pi) Y)) * (Real.sqrt (2*h+2 : ℝ))⁻¹ +
      (expressionBound E + (E.length : ℝ)) * uniformRetainedTraceError D Y H h S.card := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let V := polynomialNormalizedReconstruction (scaledCutFiniteCountReconstruction A hN P h e Y j J) n
  have hV : ‖V‖ ≤ 1 := polynomialNormalizedReconstruction_norm_le _
    (scaledCutFiniteCountReconstruction_norm_le A hN P h e Y j J) n
  have hw := retained_weighted_trace_difference (2*h) (P'.s+4) P'.epsilon_pos hY H
    (observationCylinderFilter A hN P h e qs r s hs V d)
    (observationCylinderFilter_norm_le A hN P h e qs r s hs V hV d)
  have hb := retained_expression_uniform_trace_bound E P'.epsilon_pos hD hY hH h hsmall S hfar geom
  have hpret : holomorphicSum (retainedExpression Y H E) (h+1) =
      holomorphicSum (retainedExpression Y H (countObservationFilterExpression A hN P e qs r s hs Y j J n d)) (h+1) := by
    simp only [holomorphicSum_retainedExpression, hphysical]
  rw [hpret, retained_countFilter_liftedTrace] at hb
  have hre : regularSum (retainedExpression Y H E) = fun z =>
      (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z).comp
        ((observationRegularFilter A hN P e qs r s hs z
          (polynomialNormalizedReconstruction (scaledCutFiniteRegularCountReconstruction A hN P e z Y j J) n) d).comp
          (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z)) := by
    funext z
    exact (regularSum_retainedExpression Y H E z).trans
      (congrArg (fun T : RegularSpace →L[ℂ] RegularSpace =>
        (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z).comp
          (T.comp (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z)))
        ((hregular z).trans (regularSum_countObservationFilterExpression A hN P e qs r s hs z Y j J n d)))
  rw [hre] at hb
  have hw' : |finiteRetainedFilterTrace A hN P h e qs r s hs Y H j J n d (P'.s+4) / (2*h+2 : ℝ) -
      finiteRetainedFilterTrace A hN P h e qs r s hs Y H j J n d 0 / (2*h+2 : ℝ)| ≤
      (2 * Real.sqrt (localizedErrorBound (P'.s+4) (4*Real.pi) Y) *
        Real.sqrt (massSlope (P'.s+4) (4*Real.pi) Y)) * (Real.sqrt (2*h+2 : ℝ))⁻¹ := by
    simpa only [finiteRetainedFilterTrace, Nat.cast_mul, Nat.cast_ofNat, Real.norm_eq_abs, sub_div] using hw
  apply (abs_sub_le _ (finiteRetainedFilterTrace A hN P h e qs r s hs Y H j J n d 0 / (2*h+2 : ℝ)) _).trans
  apply add_le_add hw'
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hb


#print axioms finiteRetainedFilterTrace_regular_comparison_of_replacement

theorem finiteRetainedFilterTrace_exact_regular_comparison_of_replacement (hN : 0 < N) (P : Parameters A)
    (h : ℕ) (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set UpperHalfPlane) (hs : ∀ i, IsCompact (s i))
    (Y H D : ℝ) (hY : 0 < Y) (hH : 0 < H) (hD : 0 ≤ D) (j J n d : ℕ) (hJ : 0 < J)
    (S : Finset ℤ) (hsmall : (h+1 : ℝ)^(-(1/3 : ℝ))*D ≤ 1)
    (hfar : ∀ a : ℤ, a ∉ S → 2 * compactBaseBound Y H 1 ≤ 1 + |(a : ℝ)|)
    (E : Expression)
    (hphysical : ∀ m, holomorphicSum E m = holomorphicSum (countObservationFilterExpression A hN P e qs r s hs Y j J n d) m)
    (hregular : ∀ z, regularSum E z = regularSum (countObservationFilterExpression A hN P e qs r s hs Y j J n d) z)
    (geom : ∀ b ∈ E,
      b.label ≠ 1 → RetainedBranchGeometry b Y H D S) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let B := fun z => observationRegularFilter A hN P e qs r s hs z
      (normalizedReconstruction (scaledRegularCountReconstruction A hN P e z)) d
    |finiteRetainedFilterTrace A hN P h e qs r s hs Y H j J n d (P'.s+4) / (2*h+2 : ℝ) -
      signedTrace volume (regularRetained Y H B)/(4*Real.pi)| ≤
      (2 * Real.sqrt (AsymptoticCylinderModeComparison.localizedErrorBound (P'.s+4) (4*Real.pi) Y) *
        Real.sqrt (AsymptoticCylinderModeComparison.massSlope (P'.s+4) (4*Real.pi) Y)) *
          (Real.sqrt (2*h+2 : ℝ))⁻¹ +
      (expressionBound E + (E.length : ℝ)) * uniformRetainedTraceError D Y H h S.card +
      ((2*d+2:ℝ)*normalizedCutError A P Y j J n)/(Y*(4*Real.pi)) := by
  let B := fun z => observationRegularFilter A hN P e qs r s hs z
    (normalizedReconstruction (scaledRegularCountReconstruction A hN P e z)) d
  have hb := finiteRetainedFilterTrace_regular_comparison_of_replacement A hN P h e qs r s hs
    Y H D hY hH hD j J n d S hsmall hfar E hphysical hregular geom
  have he : regularRetained Y H (regularSum E) = fun z =>
      (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z).comp
        ((observationRegularFilter A hN P e qs r s hs z
          (polynomialNormalizedReconstruction (scaledCutFiniteRegularCountReconstruction A hN P e z Y j J) n) d).comp
          (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z)) := by
    funext z
    exact congrArg (fun T : RegularSpace →L[ℂ] RegularSpace =>
      (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z).comp
        (T.comp (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z)))
      ((hregular z).trans (regularSum_countObservationFilterExpression A hN P e qs r s hs z Y j J n d))
  have ht := finiteRegularFilter_retained_trace_error A hN P e qs r s hs hY H j J n d hJ
  have hEr : regularSum E = regularSum (countObservationFilterExpression A hN P e qs r s hs Y j J n d) := funext hregular
  dsimp only at ht
  rw [←hEr] at ht
  have ht' : |signedTrace volume (regularRetained Y H (regularSum E))/(4*Real.pi)-
      signedTrace volume (regularRetained Y H B)/(4*Real.pi)| ≤
      ((2*d+2:ℝ)*normalizedCutError A P Y j J n)/(Y*(4*Real.pi)) := by
    rw [← sub_div,abs_div,abs_of_pos (by positivity : 0 < 4*Real.pi)]
    simpa only [Real.norm_eq_abs,div_div] using
      div_le_div_of_nonneg_right ht (by positivity : 0 ≤ 4*Real.pi)
  apply (abs_sub_le _ (signedTrace volume (regularRetained Y H (regularSum E))/(4*Real.pi)) _).trans
  apply add_le_add _ ht'
  rw [he]
  exact hb

#print axioms regularRetained_trace_difference
#print axioms finiteRegularFilter_retained_trace_error

#print axioms finiteRetainedFilterTrace_exact_regular_comparison_of_replacement

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
    (finiteRetainedFilterTrace_exact_regular_comparison_of_replacement A hN P h e qs r s hs
      Y H D hY hH hD j J n d hJ S hsmall hfar E hphysical hregular geom)
  have huw : u ≤ w := div_le_div_of_nonneg_right
    (observationRegularFilter_retained_trace_le_source A hN P e qs r s hs d Y H)
    (by positivity : 0 ≤ 4*Real.pi)
  change (Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P'.s) e):ℝ)/k ≤ w+_
  have he : sectorRegularTraceError A P h Y H D j J n d S.card E = (4*h+2:ℝ)/k*a+b+c := by
    dsimp [sectorRegularTraceError,a,b,c,k]
    ring
  rw [he]
  linarith


#print axioms sector_finrank_le_regular_source_trace_of_replacement

end QuantitativeHolomorphic
