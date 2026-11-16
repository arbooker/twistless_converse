module

public import QuantitativeMaassFullRegularReconstructionV1
public import QuantitativeMaassFullFilterExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency true
@[expose] public noncomputable section

open ContinuousLinearMap AsymptoticSectorSigns QuantitativeHolomorphic AsymptoticFiniteBranch
open AsymptoticCompactObservationCount Set
namespace QuantitativeMaass.EulerHilbert.FullTerminal

variable {N Q : ℕ} {hQ : 0<Q} (A : FinitenessCertificate.Certificate N Q hQ)
  (hN : 0<N) (P : FinitenessGlobalHeight.Parameters A)

theorem scaledFullExpression_regular (e : Sector N) (j J : ℕ) (z : UpperHalfPlane) :
    regularSum (scaledFullExpression A hN P e j J) z=
      ((countReconstructionBound A P)⁻¹ • finiteRegularReconstruction A hN P e z j J).comp
        (AsymptoticRegularReconstruction.TerminalSpace A
          (AsymptoticReconstructedCount.parameters A P) z).subtypeL.adjoint := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let F := AsymptoticRegularReconstruction.finiteFoldFull A hN P' (multiplier e) j
    (Finset.Icc (-(J:ℤ)) J) z
  let S := (AsymptoticRegularReconstruction.TerminalSpace A P' z).subtypeL
  let c := (countReconstructionBound A P)⁻¹
  have hright : F.comp (AsymptoticRegularCertificate.highProjection A P' z)=F :=
    AsymptoticRegularReconstruction.finiteFoldFull_right_terminal A hN P'
      (multiplier e) j (Finset.Icc (-(J:ℤ)) J) z
  have hs : S.comp S.adjoint=AsymptoticRegularCertificate.highProjection A P' z :=
    AsymptoticOrbitRegion.subtype_comp_adjoint (G:=AsymptoticRationalGroup.Group)
      (AsymptoticCertificateOperators.highStrip P'.ε) z
  have hf : (F.comp S).comp S.adjoint=F := by rw [comp_assoc,hs,hright]
  have hr : regularSum (scaledFullExpression A hN P e j J) z=(c:ℂ) • F :=
    (regularSum_scale (c:ℂ) _ z).trans
      (congrArg (fun T : AsymptoticRegularFoldedLow.Space→L[ℂ]AsymptoticRegularFoldedLow.Space =>
        (c:ℂ) • T) (regularSum_fullExpression A hN P' (multiplier e) j (Finset.Icc (-(J:ℤ)) J) z))
  apply hr.trans
  apply (RCLike.real_smul_eq_coe_smul (K:=ℂ) c F).symm.trans
  change c • F=(c • (F.comp S)).comp S.adjoint
  rw [smul_comp,hf]

theorem normalizedFullExpression_regular (e : Sector N) (n j J : ℕ) (z : UpperHalfPlane) :
    regularSum (normalizedReconstructionExpression (scaledFullExpression A hN P e j J) n) z=
      (finiteNormalizedRegularReconstruction A hN P e z n j J).comp
        (AsymptoticRegularReconstruction.TerminalSpace A
          (AsymptoticReconstructedCount.parameters A P) z).subtypeL.adjoint := by
  let S := (AsymptoticRegularReconstruction.TerminalSpace A
    (AsymptoticReconstructedCount.parameters A P) z).subtypeL
  have hS : S.adjoint.comp S=1 :=
    AsymptoticOrbitRegion.adjoint_comp_subtype (G:=AsymptoticRationalGroup.Group)
      (AsymptoticCertificateOperators.highStrip (AsymptoticReconstructedCount.parameters A P).ε) z
  have he := regularSum_normalizedReconstructionExpression (scaledFullExpression A hN P e j J) n z
  have hh := congrArg (fun T : AsymptoticRegularFoldedLow.Space→L[ℂ]AsymptoticRegularFoldedLow.Space =>
    polynomialNormalizedReconstruction T n) (scaledFullExpression_regular A hN P e j J z)
  let V := (countReconstructionBound A P)⁻¹ • finiteRegularReconstruction A hN P e z j J
  have ht := polynomialNormalizedReconstruction_transport S hS
    (1 : AsymptoticRegularFoldedLow.Space→L[ℂ]AsymptoticRegularFoldedLow.Space)
    ((norm_map_iff_adjoint_comp_self
      (1 : AsymptoticRegularFoldedLow.Space→L[ℂ]AsymptoticRegularFoldedLow.Space)).1 (fun _ => rfl)) V n
  have ht' : polynomialNormalizedReconstruction (V.comp S.adjoint) n=
      (polynomialNormalizedReconstruction V n).comp S.adjoint := by
    simpa only [one_def,id_comp] using ht
  exact he.trans (hh.trans ht')

/-- The exact common branch list has the matching regular interpretation,
including the same terminal restriction and the same row normalization. -/
theorem fullFilterExpression_regular (e : Sector N) {s : Set UpperHalfPlane}
    (hs : IsCompact s) (qs : Finset ℕ+) (n j J d : ℕ) (z : UpperHalfPlane) :
    let L := fun q : ℕ+ => AsymptoticRegularObservationRows.row hN (.twist q.val q.property) e hs
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+3) z
    let V := finiteNormalizedRegularReconstruction A hN P e z n j J
    regularSum (fullFilterExpression A hN P e hs qs n j J d) z=
      V.comp ((finiteRowFilter qs L (commonTwistBound A hN P hs) V d).comp V.adjoint) := by
  intro L V
  let S := (AsymptoticRegularReconstruction.TerminalSpace A
    (AsymptoticReconstructedCount.parameters A P) z).subtypeL
  have hS : S.adjoint.comp S=1 :=
    AsymptoticOrbitRegion.adjoint_comp_subtype (G:=AsymptoticRationalGroup.Group)
      (AsymptoticCertificateOperators.highStrip (AsymptoticReconstructedCount.parameters A P).ε) z
  let rows := fun q : ℕ+ => rowExpression hN (.twist q.val q.property) e hs
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    ((AsymptoticReconstructedCount.parameters A P).s+3)
  let b := commonTwistBound A hN P hs
  have he := regularSum_observationFilterExpression qs rows
    (normalizedReconstructionExpression (scaledFullExpression A hN P e j J) n) b d z
  have hv := normalizedFullExpression_regular A hN P e n j J z
  have hh := congrArg (fun T : AsymptoticRegularFoldedLow.Space→L[ℂ]AsymptoticRegularFoldedLow.Space =>
    T.comp ((finiteRowFilter qs (fun q => regularSum (rows q) z) b T d).comp T.adjoint)) hv
  have ht := finiteRowFilter_source_transport S hS V qs (fun q => regularSum (rows q) z) b d
  have hr : (fun q => regularSum (rows q) z)=L := by
    funext q
    exact regularSum_rowExpression hN (.twist q.val q.property) e hs _ _ z
  have hf := congrArg (fun M : ℕ+→AsymptoticRegularFoldedLow.Space→L[ℂ]AsymptoticRegularFoldedLow.Space =>
    V.comp ((finiteRowFilter qs M b V d).comp V.adjoint)) hr
  exact he.trans (hh.trans (ht.trans hf))

/-- Physical and regular finite-branch approximation have the same explicit
error at every orbit root. -/
theorem fullFilterExpression_regular_error (e : Sector N) {s : Set UpperHalfPlane}
    (hs : IsCompact s) (qs : Finset ℕ+) (n j J d : ℕ) (hJ : 0<J) (z : UpperHalfPlane) :
    let L := fun q : ℕ+ => AsymptoticRegularObservationRows.row hN (.twist q.val q.property) e hs
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+3) z
    let U := normalizedRegularReconstruction A hN P e z
    ‖regularSum (fullFilterExpression A hN P e hs qs n j J d) z-
      U.comp ((finiteRowFilter qs L (commonTwistBound A hN P hs) U d).comp U.adjoint)‖ ≤
      (2*d+2 : ℝ) *
        (countReconstructionError A P j J*(1+3*(3^n:ℕ))*(7:ℝ)^(4^n)+
          (1-countGramLower A P)^(2^n)/Real.sqrt (countGramLower A P)) := by
  intro L U
  let V := finiteNormalizedRegularReconstruction A hN P e z n j J
  let b := commonTwistBound A hN P hs
  have he := congrArg (fun T : AsymptoticRegularFoldedLow.Space→L[ℂ]AsymptoticRegularFoldedLow.Space =>
    ‖T-U.comp ((finiteRowFilter qs L b U d).comp U.adjoint)‖)
    (fullFilterExpression_regular A hN P e hs qs n j J d z)
  apply he.trans_le
  have hU : ‖U‖≤1 := by
    apply opNorm_le_bound _ zero_le_one
    intro x
    exact (normalizedRegularReconstruction_norm A hN P e z x).le.trans_eq (one_mul ‖x‖).symm
  exact (finiteRowFilter_sandwich_difference qs L _
    (fun q => regular_row_norm_le_physical_bound hN (.twist q.val q.property) e hs
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+3) z) U
    (finiteNormalizedRegularReconstruction A hN P e z n j J) hU
    (finiteNormalizedRegularReconstruction_norm A hN P e z n j J) d).trans
    (mul_le_mul_of_nonneg_left (finiteNormalizedRegularReconstruction_error A hN P e z n j J hJ)
      (by positivity))

#print axioms scaledFullExpression_regular
#print axioms normalizedFullExpression_regular
#print axioms fullFilterExpression_regular
#print axioms fullFilterExpression_regular_error
end QuantitativeMaass.EulerHilbert.FullTerminal
