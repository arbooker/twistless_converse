module

public import QuantitativeHolomorphicTerminalFiniteNormalizerV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCompactObservationCount AsymptoticFiniteBranch AsymptoticRegularTrace MeasureTheory
open scoped ENNReal

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) {ι : Type*}

/-- Compare on the fixed terminal source, whose area is epsilon inverse.
The physical lower cutoff Y no longer occurs in the trace-loss denominator. -/
theorem finiteRegularFilter_retained_trace_le_source (hN : 0<N) (P : Parameters A)
    (e : Sector N) (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane)
    (hs : ∀ i, IsCompact (s i)) {Y : ℝ} (hY : 0≤Y) (H : ℝ)
    (j J n d : ℕ) (hJ : 0<J) :
    signedTrace volume (regularRetained Y H
      (regularSum (countObservationFilterExpression A hN P e qs r s hs Y j J n d))) ≤
    signedTrace volume (fun z => (regularSourceFilter A hN P e qs r s hs d z).comp
      (AsymptoticOrbitDiagonal.corner
        (AsymptoticCertificateOperators.highStrip (AsymptoticReconstructedCount.parameters A P).ε) z)) +
      countFilterError A P Y j J n d/(AsymptoticReconstructedCount.parameters A P).ε := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let rows := fun i => rowExpression hN (r i) e (hs i) P'.epsilon_pos (P'.s+4)
  let L := fun i z => regularSum (rows i) z
  let b := fun i => rowBound hN (r i) (hs i) P'.epsilon_pos (P'.s+4)
  let U := normalizedRegularAmbientCountReconstruction A hN P e
  let V := finiteNormalizedRegularAmbient A hN P e Y j J n
  let FU := fun z => finiteRowFilter qs (fun i => L i z) b (U z) d
  let FV := fun z => finiteRowFilter qs (fun i => L i z) b (V z) d
  let GU := fun z => (U z).adjoint.comp (U z)
  let GV := fun z => (V z).adjoint.comp (V z)
  let CU := fun z => (FU z).comp (GU z)
  let CV := fun z => (FV z).comp (GV z)
  let E := countObservationFilterExpression A hN P e qs r s hs Y j J n d
  have hL (i : ι) (z : UpperHalfPlane) : ‖L i z‖≤b i := by
    dsimp only [L,rows,b]
    rw [regularSum_rowExpression]
    exact regular_row_norm_le_physical_bound hN (r i) e (hs i) P'.epsilon_pos (P'.s+4) z
  have hU := normalizedRegularAmbientCountReconstruction_norm_le A hN P e
  have hV := finiteNormalizedRegularAmbient_norm_le A hN P e Y j J n
  have hFU (z : UpperHalfPlane) : ‖FU z‖≤1 :=
    (finiteRowFilter_order qs (fun i => L i z) b (fun i => hL i z) (U z) (hU z) d).2.2
  have hFV (z : UpperHalfPlane) : ‖FV z‖≤1 :=
    (finiteRowFilter_order qs (fun i => L i z) b (fun i => hL i z) (V z) (hV z) d).2.2
  have hmV := regularSum_matrix_measurable
    (normalizedReconstructionExpression (scaledCutCountExpression A hN P e Y j J) n)
  have hcV := regularSum_covariant
    (normalizedReconstructionExpression (scaledCutCountExpression A hN P e Y j J) n)
  have hrU := normalizedRegularCountReconstruction_regular A hN P e
  have hrFU := finiteRowFilter_regular qs L b U
    (fun i => regularSum_matrix_measurable (rows i))
    (fun i => regularSum_covariant (rows i)) hrU.1 hrU.2 d
  have hrFV := finiteRowFilter_regular qs L b V
    (fun i => regularSum_matrix_measurable (rows i))
    (fun i => regularSum_covariant (rows i)) hmV hcV d
  have hmGU := matrix_comp_measurable (fun z => (U z).adjoint) U
    (matrix_adjoint_measurable U hrU.1) hrU.1
  have hmGV := matrix_comp_measurable (fun z => (V z).adjoint) V
    (matrix_adjoint_measurable V hmV) hmV
  have hmCU := matrix_comp_measurable FU GU hrFU.1 hmGU
  have hmCV := matrix_comp_measurable FV GV hrFV.1 hmGV
  have hCU (z : UpperHalfPlane) : ‖CU z‖≤1 :=
    (opNorm_comp_le _ _).trans ((mul_le_mul (hFU z) (contraction_gram_norm_le _ (hU z))
      (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hCV (z : UpperHalfPlane) : ‖CV z‖≤1 :=
    (opNorm_comp_le _ _).trans ((mul_le_mul (hFV z) (contraction_gram_norm_le _ (hV z))
      (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hGU (z : UpperHalfPlane) : GU z=AsymptoticOrbitDiagonal.corner
      (AsymptoticCertificateOperators.highStrip P'.ε) z :=
    normalizedRegularAmbientCountReconstruction_gram A hN P e z
  have hsU (z : UpperHalfPlane) : (CU z).comp (AsymptoticOrbitDiagonal.corner
      (AsymptoticCertificateOperators.highStrip P'.ε) z)=CU z := by
    dsimp only [CU]
    rw [hGU,comp_assoc,AsymptoticOrbitDiagonal.corner_idempotent]
  have hsV (z : UpperHalfPlane) : (CV z).comp (AsymptoticOrbitDiagonal.corner
      (AsymptoticCertificateOperators.highStrip P'.ε) z)=CV z := by
    dsimp only [CV,GV]
    rw [comp_assoc,comp_assoc,finiteNormalizedRegularAmbient_right_terminal]
  have hd (z : UpperHalfPlane) : ‖CV z-CU z‖≤countFilterError A P Y j J n d :=
    (finiteRowFilter_sourceProduct_difference qs (fun i => L i z) b (fun i => hL i z)
      (U z) (V z) (hU z) (hV z) d).trans
        (mul_le_mul_of_nonneg_left (finiteNormalizedRegularAmbient_error A hN P e hY j J n hJ z) (by positivity))
  have harea : volume (AsymptoticCertificateOperators.highStrip P'.ε)=ENNReal.ofReal P'.ε⁻¹ :=
    AsymptoticHyperbolicArea.closed_terminal_area P'.epsilon_pos
  have hfinite : volume (AsymptoticCertificateOperators.highStrip P'.ε)<∞ := by
    rw [harea]
    exact ENNReal.ofReal_lt_top
  have hdiff := norm_signedTrace_sub_le_corner volume
    (AsymptoticCertificateOperators.highStrip_measurable P'.ε) hfinite CV CU
    (hmCV 1 1) (hmCU 1 1) hCV hCU hsV hsU hd
  rw [harea,ENNReal.toReal_ofReal (inv_nonneg.mpr P'.epsilon_pos.le),←div_eq_mul_inv] at hdiff
  have he (z : UpperHalfPlane) : regularSum E z=(V z).comp ((FV z).comp (V z).adjoint) := by
    exact regularSum_observationFilterExpression qs rows
      (normalizedReconstructionExpression (scaledCutCountExpression A hN P e Y j J) n) b d z
  have hf := finiteNormalizedRegularAmbient_gram_trace_finite A hN P e Y j J n
  have hcyclic := signedTrace_sandwich volume AsymptoticRationalGroup.measurePreserving V FV
    hmV hrFV.1 hcV hrFV.2 hf hFV
  have hEpos (z : UpperHalfPlane) : (regularSum E z).IsPositive := by
    rw [he]
    have hp := nonneg_iff_isPositive.mp
      (finiteRowFilter_order qs (fun i => L i z) b (fun i => hL i z) (V z) (hV z) d).1
    simpa only [adjoint_adjoint,comp_assoc] using hp.adjoint_conj (V z).adjoint
  have hEfin : AsymptoticRegularTrace.trace volume (regularSum E)<∞ := by
    have ht := trace_sandwich_le_range_gram volume V FV hFV
    simp only [←he] at ht
    apply ht.trans_lt
    rw [←rational_trace_adjoint_mul V hmV hcV]
    exact hf
  have hret := regularRetained_trace_le_full Y H (regularSum E) (regularSum_matrix_measurable E) hEpos hEfin
  have hfull : signedTrace volume (regularSum E)=signedTrace volume CV := by
    exact (congrArg (signedTrace volume) (funext he)).trans hcyclic
  have hsource : CU=fun z => (regularSourceFilter A hN P e qs r s hs d z).comp
      (AsymptoticOrbitDiagonal.corner (AsymptoticCertificateOperators.highStrip P'.ε) z) := by
    funext z
    have hfilter : FU z=regularSourceFilter A hN P e qs r s hs d z := by
      dsimp only [FU,L,rows,U,b,regularSourceFilter,P']
      simp only [regularSum_rowExpression]
    exact congrArg₂ (fun X Z : RegularSpace →L[ℂ] RegularSpace => X.comp Z) hfilter (hGU z)
  have habdiff : |signedTrace volume CV-signedTrace volume CU| ≤
      countFilterError A P Y j J n d/P'.ε := by
    simpa only [Real.norm_eq_abs] using hdiff
  have hsourceTrace := congrArg (signedTrace volume) hsource
  change signedTrace volume (regularRetained Y H (regularSum E)) ≤ _
  linarith only [hret,hfull,hsourceTrace,habdiff,
    le_abs_self (signedTrace volume CV-signedTrace volume CU)]

#print axioms finiteRegularFilter_retained_trace_le_source

end QuantitativeHolomorphic
