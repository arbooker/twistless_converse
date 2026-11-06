module

public import QuantitativeEulerDiamondObservationV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane QuantitativeEulerDiamondDecode AsymptoticIntegralSubgroup
open AsymptoticRationalBranches AsymptoticRationalFreeness AsymptoticCompactBranch
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

/-- Rational translations have transport norm at most one, uniformly in
the denominator, compact region, cap cutoff and weight exponent. This is
the actual full-orbit transport; no invariance of the vector is assumed. -/
theorem rational_translation_transport_norm (r : ℚ) {s : Set ℍ}
    (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    ‖branchTransport (symbolBranch (translationLabel r)) hs hε t x‖≤1 := by
  apply branchTransport_norm_of_ratio _ hs hε zero_le_one t x
  intro z _
  rw [ratio,←ofMatrix_action _ (symbolBranch (translationLabel r)).positive z,
    symbolBranch_label,AsymptoticCompactTranslation.cap_translate,
    div_self (cap_pos hε t z).ne']

theorem compact_right_translation_norm (r : ℚ) (A : Ring) {s : Set ℍ}
    (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (v : Space) :
    ‖compactAction hs hε t x (A*symbol (translationLabel r)) v‖≤
      ‖compactAction (branchImage_compact (symbolBranch (translationLabel r)) hs)
        hε t x A v‖ := by
  have h := (branchTransport (symbolBranch (translationLabel r)) hs hε t x).le_of_opNorm_le
    (rational_translation_transport_norm r hs hε t x)
    (compactAction (branchImage_compact (symbolBranch (translationLabel r)) hs) hε t x A v)
  have he := congrArg (fun T : Space →L[ℂ] Space => ‖T v‖)
    (compactAction_mul_symbol (symbolBranch (translationLabel r)) hs hε t x A)
  simp only [symbolBranch_label,ContinuousLinearMap.comp_apply] at he
  exact he.trans_le (h.trans_eq (one_mul _))

#print axioms rational_translation_transport_norm
#print axioms compact_right_translation_norm
end QuantitativeEulerEndpointPrepared
