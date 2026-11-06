module

public import QuantitativeHolomorphicRegularClosureV1
public import QuantitativeHolomorphicFilterComparisonV1
public import AsymptoticSignedCornerContinuityV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCompactObservationCount AsymptoticFiniteBranch AsymptoticRegularTrace MeasureTheory
open AsymptoticObservation AsymptoticUnweightedKernel
open scoped ENNReal

def regularRetained (Y H : ℝ) (B : UpperHalfPlane → RegularSpace →L[ℂ] RegularSpace)
    (z : UpperHalfPlane) :=
  (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z).comp
    ((B z).comp (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z))

theorem regularRetained_norm_le (Y H : ℝ)
    (B : UpperHalfPlane → RegularSpace →L[ℂ] RegularSpace) (z : UpperHalfPlane) :
    ‖regularRetained Y H B z‖ ≤ ‖B z‖ := by
  have hp := AsymptoticOrbitRegion.corner_norm_le
    (G := AsymptoticRationalGroup.Group) (retainedRegion Y H) z
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans
  rw [one_mul]
  apply (opNorm_comp_le _ _).trans
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (norm_nonneg (B z))

theorem regularRetained_matrix_measurable (Y H : ℝ)
    (B : UpperHalfPlane → RegularSpace →L[ℂ] RegularSpace)
    (hm : ∀ g h, Measurable (fun z => matrix (B z) g h))
    (g h : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (regularRetained Y H B z) g h) := by
  have hc := AsymptoticOrbitDiagonal.corner_matrix_measurable
    (fun a => (AsymptoticRationalGroup.measurePreserving a).measurable)
    (retainedRegion_measurable Y H)
  exact matrix_comp_measurable _ _ hc (matrix_comp_measurable _ _ hm hc) g h

/-- The retained regular trace is Lipschitz with constant at most `1/Y`.
Measurability is enough; no positivity or trace-continuity premise is used. -/
theorem regularRetained_trace_difference {Y : ℝ} (hY : 0 < Y) (H : ℝ)
    (B C : UpperHalfPlane → RegularSpace →L[ℂ] RegularSpace) {CB CC δ : ℝ}
    (hmB : ∀ g h, Measurable (fun z => matrix (B z) g h))
    (hmC : ∀ g h, Measurable (fun z => matrix (C z) g h))
    (hB : ∀ z, ‖B z‖ ≤ CB) (hC : ∀ z, ‖C z‖ ≤ CC)
    (hd : ∀ z, ‖B z-C z‖ ≤ δ) :
    ‖signedTrace volume (regularRetained Y H B)-
      signedTrace volume (regularRetained Y H C)‖ ≤ δ/Y := by
  have hδ : 0 ≤ δ := (norm_nonneg (B UpperHalfPlane.I-C UpperHalfPlane.I)).trans
    (hd UpperHalfPlane.I)
  have harea : (volume : Measure UpperHalfPlane) (retainedRegion Y H) ≤
      ENNReal.ofReal Y⁻¹ := by
    apply (measure_mono (show retainedRegion Y H ⊆
      AsymptoticHyperbolicArea.closedTerminal Y from fun _ hz => ⟨hz.1,hz.2.1⟩)).trans_eq
    exact AsymptoticHyperbolicArea.closed_terminal_area hY
  have hfinite := harea.trans_lt ENNReal.ofReal_lt_top
  have hsupp (F : UpperHalfPlane → RegularSpace →L[ℂ] RegularSpace) (z : UpperHalfPlane) :
      (regularRetained Y H F z).comp
        (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z)=regularRetained Y H F z := by
    simp only [regularRetained,comp_assoc,AsymptoticOrbitDiagonal.corner_idempotent]
  have he (z : UpperHalfPlane) : regularRetained Y H B z-regularRetained Y H C z=
      regularRetained Y H (fun x => B x-C x) z := by
    simp only [regularRetained,sub_comp,comp_sub]
  have hb := norm_signedTrace_sub_le_corner volume (retainedRegion_measurable Y H)
    hfinite (regularRetained Y H B) (regularRetained Y H C)
    (regularRetained_matrix_measurable Y H B hmB 1 1)
    (regularRetained_matrix_measurable Y H C hmC 1 1)
    (fun z => (regularRetained_norm_le Y H B z).trans (hB z))
    (fun z => (regularRetained_norm_le Y H C z).trans (hC z))
    (hsupp B) (hsupp C)
    (fun z => by rw [he]; exact (regularRetained_norm_le Y H _ z).trans (hd z))
  apply hb.trans
  rw [div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left _ hδ
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top harea).trans_eq
    (ENNReal.toReal_ofReal (inv_nonneg.mpr hY.le))

private theorem contraction_sandwich_norm_le {G H : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : G →L[ℂ] H) (F : G →L[ℂ] G) (hV : ‖V‖ ≤ 1) (hF : ‖F‖ ≤ 1) :
    ‖V.comp (F.comp V.adjoint)‖ ≤ 1 := by
  have ha : ‖V.adjoint‖ ≤ 1 := by rwa [adjoint.norm_map]
  have hi : ‖F.comp V.adjoint‖ ≤ 1 := by
    exact (opNorm_comp_le _ _).trans (by simpa only [one_mul] using mul_le_mul hF ha (norm_nonneg _) zero_le_one)
  exact (opNorm_comp_le _ _).trans (by simpa only [one_mul] using mul_le_mul hV hi (norm_nonneg _) zero_le_one)

variable {N Q : ℕ} {hQ : 0 < Q} (A : Certificate N Q hQ)
variable {ι : Type*}

theorem observationRegularFilter_norm_le (hN : 0 < N) (P : Parameters A)
    (e : Sector N) (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane)
    (hs : ∀ i, IsCompact (s i)) (z : UpperHalfPlane)
    (V : (AsymptoticRegularReconstruction.TerminalSpace A
      (AsymptoticReconstructedCount.parameters A P) z) →L[ℂ] RegularSpace)
    (hV : ‖V‖ ≤ 1) (d : ℕ) :
    ‖observationRegularFilter A hN P e qs r s hs z V d‖ ≤ 1 :=
  contraction_sandwich_norm_le V _ hV (finiteRowFilter_order qs _ _
    (fun i => regular_row_norm_le_physical_bound hN (r i) e (hs i)
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4) z) V hV d).2.2

/-- Explicit finite-to-exact trace replacement for the actual common global
filter. There is no measurability, regularity, or trace estimate assumption. -/
theorem finiteRegularFilter_retained_trace_error (hN : 0 < N) (P : Parameters A)
    (e : Sector N) (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane)
    (hs : ∀ i, IsCompact (s i)) {Y : ℝ} (hY : 0 < Y) (H : ℝ)
    (j J n d : ℕ) (hJ : 0 < J) :
    let E := countObservationFilterExpression A hN P e qs r s hs Y j J n d
    let B := fun z => observationRegularFilter A hN P e qs r s hs z
      (normalizedReconstruction (scaledRegularCountReconstruction A hN P e z)) d
    ‖signedTrace volume (regularRetained Y H (regularSum E))-
      signedTrace volume (regularRetained Y H B)‖ ≤
        ((2*d+2:ℝ)*normalizedCutError A P Y j J n)/Y := by
  let E := countObservationFilterExpression A hN P e qs r s hs Y j J n d
  let B := fun z => observationRegularFilter A hN P e qs r s hs z
    (normalizedReconstruction (scaledRegularCountReconstruction A hN P e z)) d
  have hB (z : UpperHalfPlane) : ‖B z‖ ≤ 1 := by
    apply observationRegularFilter_norm_le
    apply opNorm_le_bound _ zero_le_one
    intro g
    rw [normalizedRegularCountReconstruction_norm,one_mul]
  exact regularRetained_trace_difference hY H (regularSum E) B
    (regularSum_matrix_measurable E)
    (observationRegularFilter_regular A hN P e qs r s hs d).1
    (regularSum_norm_le E) hB
    (fun z => countObservationFilterExpression_regular_error A hN P e qs r s hs z Y hY.le j J n d hJ)

/-- Actual weighted holomorphic trace versus the exact normalized regular
filter. Every approximation term is explicit; the sole remaining geometric
input is an integer-matrix certificate for the displayed finite expression. -/
theorem finiteRetainedFilterTrace_exact_regular_comparison (hN : 0 < N) (P : Parameters A)
    (h : ℕ) (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set UpperHalfPlane) (hs : ∀ i, IsCompact (s i))
    (Y H D : ℝ) (hY : 0 < Y) (hH : 0 < H) (hD : 0 ≤ D) (j J n d : ℕ) (hJ : 0 < J)
    (S : Finset ℤ) (hsmall : (h+1 : ℝ)^(-(1/3 : ℝ))*D ≤ 1)
    (hfar : ∀ a : ℤ, a ∉ S → 2 * compactBaseBound Y H 1 ≤ 1 + |(a : ℝ)|)
    (geom : ∀ b ∈ countObservationFilterExpression A hN P e qs r s hs Y j J n d,
      b.label ≠ 1 → RetainedBranchGeometry b Y H D S) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let E := countObservationFilterExpression A hN P e qs r s hs Y j J n d
    let B := fun z => observationRegularFilter A hN P e qs r s hs z
      (normalizedReconstruction (scaledRegularCountReconstruction A hN P e z)) d
    |finiteRetainedFilterTrace A hN P h e qs r s hs Y H j J n d (P'.s+4) / (2*h+2 : ℝ) -
      signedTrace volume (regularRetained Y H B)/(4*Real.pi)| ≤
      (2 * Real.sqrt (AsymptoticCylinderModeComparison.localizedErrorBound (P'.s+4) (4*Real.pi) Y) *
        Real.sqrt (AsymptoticCylinderModeComparison.massSlope (P'.s+4) (4*Real.pi) Y)) *
          (Real.sqrt (2*h+2 : ℝ))⁻¹ +
      (expressionBound E + (E.length : ℝ)) * uniformRetainedTraceError D Y H h S.card +
      ((2*d+2:ℝ)*normalizedCutError A P Y j J n)/(Y*(4*Real.pi)) := by
  let E := countObservationFilterExpression A hN P e qs r s hs Y j J n d
  let B := fun z => observationRegularFilter A hN P e qs r s hs z
    (normalizedReconstruction (scaledRegularCountReconstruction A hN P e z)) d
  have hb := finiteRetainedFilterTrace_regular_comparison A hN P h e qs r s hs
    Y H D hY hH hD j J n d S hsmall hfar geom
  have he : regularRetained Y H (regularSum E) = fun z =>
      (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z).comp
        ((observationRegularFilter A hN P e qs r s hs z
          (polynomialNormalizedReconstruction (scaledCutFiniteRegularCountReconstruction A hN P e z Y j J) n) d).comp
          (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z)) := by
    funext z
    exact congrArg (fun T : RegularSpace →L[ℂ] RegularSpace =>
      (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z).comp
        (T.comp (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z)))
      (regularSum_countObservationFilterExpression A hN P e qs r s hs z Y j J n d)
  have ht := finiteRegularFilter_retained_trace_error A hN P e qs r s hs hY H j J n d hJ
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
#print axioms finiteRetainedFilterTrace_exact_regular_comparison

end QuantitativeHolomorphic
