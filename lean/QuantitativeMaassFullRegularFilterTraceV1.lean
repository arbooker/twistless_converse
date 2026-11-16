module

public import QuantitativeMaassFullRegularSourceV1
public import QuantitativeHolomorphicRegularSourceTraceV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open ContinuousLinearMap AsymptoticSectorSigns QuantitativeHolomorphic AsymptoticFiniteBranch
open AsymptoticCompactObservationCount AsymptoticRegularTrace MeasureTheory Set
open scoped ENNReal
namespace QuantitativeMaass.EulerHilbert.FullTerminal

variable {N Q : ℕ} {hQ : 0<Q} (A : FinitenessCertificate.Certificate N Q hQ)
  (hN : 0<N) (P : FinitenessGlobalHeight.Parameters A)

def fullRegularRows (e : Sector N) {s : Set UpperHalfPlane} (hs : IsCompact s)
    (q : ℕ+) (z : UpperHalfPlane) : RegularSpace→L[ℂ]RegularSpace :=
  AsymptoticRegularObservationRows.row hN (.twist q.val q.property) e hs
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    ((AsymptoticReconstructedCount.parameters A P).s+3) z

def fullRegularSourceFilter (e : Sector N) {s : Set UpperHalfPlane} (hs : IsCompact s)
    (qs : Finset ℕ+) (d : ℕ) (z : UpperHalfPlane) :=
  finiteRowFilter qs (fun q => fullRegularRows A hN P e hs q z)
    (commonTwistBound A hN P hs) (normalizedRegularAmbient A hN P e z) d

def fullRegularFilter (e : Sector N) {s : Set UpperHalfPlane} (hs : IsCompact s)
    (qs : Finset ℕ+) (d : ℕ) (z : UpperHalfPlane) :=
  (normalizedRegularAmbient A hN P e z).comp
    ((fullRegularSourceFilter A hN P e hs qs d z).comp
      (normalizedRegularAmbient A hN P e z).adjoint)

/-- The ambient source filter is the very same terminal sandwich that
occurs in the common finite-expression approximation. -/
theorem fullRegularFilter_eq_terminal (e : Sector N) {s : Set UpperHalfPlane}
    (hs : IsCompact s) (qs : Finset ℕ+) (d : ℕ) (z : UpperHalfPlane) :
    fullRegularFilter A hN P e hs qs d z=
      (normalizedRegularReconstruction A hN P e z).comp
        ((finiteRowFilter qs (fun q => fullRegularRows A hN P e hs q z)
          (commonTwistBound A hN P hs) (normalizedRegularReconstruction A hN P e z) d).comp
          (normalizedRegularReconstruction A hN P e z).adjoint) := by
  let S := (AsymptoticRegularReconstruction.TerminalSpace A
    (AsymptoticReconstructedCount.parameters A P) z).subtypeL
  have hS : S.adjoint.comp S=1 :=
    AsymptoticOrbitRegion.adjoint_comp_subtype (G:=AsymptoticRationalGroup.Group)
      (AsymptoticCertificateOperators.highStrip (AsymptoticReconstructedCount.parameters A P).ε) z
  exact finiteRowFilter_source_transport S hS
    (normalizedRegularReconstruction A hN P e z) qs _ _ d

theorem fullFilterExpression_exact_regular_error (e : Sector N) {s : Set UpperHalfPlane}
    (hs : IsCompact s) (qs : Finset ℕ+) (n j J d : ℕ) (hJ : 0<J) (z : UpperHalfPlane) :
    ‖regularSum (fullFilterExpression A hN P e hs qs n j J d) z-
      fullRegularFilter A hN P e hs qs d z‖≤(2*d+2 : ℝ)*normalizedCutError A P 0 j J n := by
  have he := congrArg (fun T : RegularSpace→L[ℂ]RegularSpace =>
    ‖regularSum (fullFilterExpression A hN P e hs qs n j J d) z-T‖)
    (fullRegularFilter_eq_terminal A hN P e hs qs d z)
  apply he.trans_le
  simpa only [fullRegularRows,normalizedCutError,cutCountReconstructionError,zero_div,zero_mul,add_zero] using
    fullFilterExpression_regular_error A hN P e hs qs n j J d hJ z

theorem fullRegularSourceFilter_norm (e : Sector N) {s : Set UpperHalfPlane}
    (hs : IsCompact s) (qs : Finset ℕ+) (d : ℕ) (z : UpperHalfPlane) :
    ‖fullRegularSourceFilter A hN P e hs qs d z‖≤1 :=
  (finiteRowFilter_order qs _ _
    (fun q => regular_row_norm_le_physical_bound hN (.twist q.val q.property) e hs
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+3) z) _
    (normalizedRegularAmbient_norm A hN P e z) d).2.2

theorem fullRegularSourceFilter_positive (e : Sector N) {s : Set UpperHalfPlane}
    (hs : IsCompact s) (qs : Finset ℕ+) (d : ℕ) (z : UpperHalfPlane) :
    (fullRegularSourceFilter A hN P e hs qs d z).IsPositive :=
  nonneg_iff_isPositive.mp (finiteRowFilter_order qs _ _
    (fun q => regular_row_norm_le_physical_bound hN (.twist q.val q.property) e hs
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+3) z) _
    (normalizedRegularAmbient_norm A hN P e z) d).1

theorem fullRegularSourceFilter_regular (e : Sector N) {s : Set UpperHalfPlane}
    (hs : IsCompact s) (qs : Finset ℕ+) (d : ℕ) :
    (∀ g h, Measurable (fun z => matrix (fullRegularSourceFilter A hN P e hs qs d z) g h)) ∧
      Covariant (fullRegularSourceFilter A hN P e hs qs d) := by
  let rows := fun q : ℕ+ => rowExpression hN (.twist q.val q.property) e hs
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    ((AsymptoticReconstructedCount.parameters A P).s+3)
  have he (q : ℕ+) : regularSum (rows q)=fullRegularRows A hN P e hs q :=
    funext (fun z => regularSum_rowExpression hN (.twist q.val q.property) e hs _ _ z)
  apply finiteRowFilter_regular
  · intro q
    exact (congrArg (fun W : UpperHalfPlane→RegularSpace→L[ℂ]RegularSpace =>
      ∀ g h,Measurable (fun z => matrix (W z) g h)) (he q)).mp
      (regularSum_matrix_measurable (rows q))
  · intro q
    exact (congrArg Covariant (he q)).mp (regularSum_covariant (rows q))
  · exact (normalizedRegularAmbient_regular A hN P e).1
  · exact (normalizedRegularAmbient_regular A hN P e).2

/-- Cyclicity transfers the actual raw full-terminal filter trace to its
finite-area terminal source. The source decay estimate is a separate step. -/
theorem fullRegularFilter_trace_eq_source (e : Sector N) {s : Set UpperHalfPlane}
    (hs : IsCompact s) (qs : Finset ℕ+) (d : ℕ) :
    signedTrace volume (fullRegularFilter A hN P e hs qs d)=
      signedTrace volume (fun z => (fullRegularSourceFilter A hN P e hs qs d z).comp
        (AsymptoticOrbitDiagonal.corner
          (AsymptoticCertificateOperators.highStrip (AsymptoticReconstructedCount.parameters A P).ε) z)) := by
  have hU := normalizedRegularAmbient_regular A hN P e
  have hF := fullRegularSourceFilter_regular A hN P e hs qs d
  have ht : AsymptoticRegularTrace.trace volume (fun z =>
      (normalizedRegularAmbient A hN P e z).adjoint.comp
        (normalizedRegularAmbient A hN P e z))<∞ := by
    rw [normalizedRegularAmbient_trace_gram]
    exact ENNReal.ofReal_lt_top
  have hh := signedTrace_sandwich volume AsymptoticRationalGroup.measurePreserving
    (normalizedRegularAmbient A hN P e) (fullRegularSourceFilter A hN P e hs qs d)
    hU.1 hF.1 hU.2 hF.2 ht (fullRegularSourceFilter_norm A hN P e hs qs d)
  change signedTrace volume (fun z => (normalizedRegularAmbient A hN P e z).comp
    ((fullRegularSourceFilter A hN P e hs qs d z).comp
      (normalizedRegularAmbient A hN P e z).adjoint))=_
  simpa only [normalizedRegularAmbient_gram] using hh

theorem fullRegularFilter_trace_finite (e : Sector N) {s : Set UpperHalfPlane}
    (hs : IsCompact s) (qs : Finset ℕ+) (d : ℕ) :
    AsymptoticRegularTrace.trace volume (fullRegularFilter A hN P e hs qs d)<∞ := by
  have hU := normalizedRegularAmbient_regular A hN P e
  have he := rational_trace_adjoint_mul (normalizedRegularAmbient A hN P e) hU.1 hU.2
  have ht := trace_sandwich_le_range_gram volume
    (normalizedRegularAmbient A hN P e) (fullRegularSourceFilter A hN P e hs qs d)
    (fullRegularSourceFilter_norm A hN P e hs qs d)
  apply ht.trans_lt
  rw [←he,normalizedRegularAmbient_trace_gram]
  exact ENNReal.ofReal_lt_top

#print axioms fullFilterExpression_exact_regular_error
#print axioms fullRegularFilter_eq_terminal
#print axioms fullRegularSourceFilter_norm
#print axioms fullRegularSourceFilter_positive
#print axioms fullRegularSourceFilter_regular
#print axioms fullRegularFilter_trace_eq_source
#print axioms fullRegularFilter_trace_finite
end QuantitativeMaass.EulerHilbert.FullTerminal
