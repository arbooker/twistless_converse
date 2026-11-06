module

public import QuantitativeArithmeticRetainedFilterTraceV1
public import QuantitativeArithmeticRetainedFiniteTransportV1
public import QuantitativeHolomorphicRegularSourceV1
public import QuantitativeHolomorphicQuantifiedComplexityV1
public import QuantitativeArithmeticRetainedScheduleGrowthV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedFilterExpression
open UpperHalfPlane ContinuousLinearMap MeasureTheory AsymptoticSectorSigns
open AsymptoticFiniteBranch AsymptoticCompactObservationCount AsymptoticRegularTrace
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedSectorReconstruction
open QuantitativeArithmeticRetainedPreparedReconstruction
open QuantitativeArithmeticRetainedFiniteNormalization
open QuantitativeArithmeticRetainedFiniteTransport QuantitativeHolomorphic
open scoped ENNReal

section Operators
variable {G H K : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace G] [CompleteSpace H] in
private theorem isometry_bound (U : G →L[ℂ] H) (hU : ∀v,‖U v‖=‖v‖) : ‖U‖≤1 := by
  apply opNorm_le_bound _ zero_le_one
  intro v
  rw [hU,one_mul]

private theorem subtype_adjoint_bound (W : Submodule ℂ H) [CompleteSpace W] :
    ‖W.subtypeL.adjoint‖≤1 := by
  rw [adjoint.norm_map]
  apply opNorm_le_bound _ zero_le_one
  intro v
  simp

private theorem extended_gram (U : G →L[ℂ] H) (I : G →L[ℂ] K) (hU : U.adjoint.comp U=1) :
    (U.comp I.adjoint).adjoint.comp (U.comp I.adjoint)=I.comp I.adjoint := by
  rw [adjoint_comp,adjoint_adjoint,comp_assoc,←comp_assoc U.adjoint U,hU]
  simp only [one_def,id_comp]
end Operators

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ)
    (P : Parameters A) (hS : ∀p∈S,p.Prime) (hN : 0<N)

/-- The normalized mixed regular reconstruction, zero off its actual terminal source. -/
def regularAmbient (e : Sector N) (z : ℍ) : RegularSpace →L[ℂ] RegularSpace :=
  (QuantitativeArithmeticRetainedRegularNormalization.normalized A hS hN P
    (multiplier e) (ramifiedParameter e) (by omega : 2≤exponent A P+3) z).comp
    (QuantitativeArithmeticRetainedRegularExtension.TerminalSpace A P z).subtypeL.adjoint

theorem regularAmbient_norm (e : Sector N) (z : ℍ) : ‖regularAmbient A P hS hN e z‖≤1 := by
  have hu := isometry_bound _ (QuantitativeArithmeticRetainedRegularNormalization.normalized_norm A hS hN P
    (multiplier e) (ramifiedParameter e) (fun q _ => multiplier_norm e q)
    (fun p _ => ramifiedParameter_norm e p) (by omega : 2≤exponent A P+3) z
    (regular_contraction A P hS hN e z))
  have hi := subtype_adjoint_bound (QuantitativeArithmeticRetainedRegularExtension.TerminalSpace A P z)
  exact (opNorm_comp_le _ _).trans ((mul_le_mul hu hi (norm_nonneg _) zero_le_one).trans_eq (one_mul _))

theorem regularAmbient_regular (e : Sector N) :
    (∀g h,Measurable (fun z => matrix (regularAmbient A P hS hN e z) g h)) ∧
      Covariant (regularAmbient A P hS hN e) := by
  apply regular_of_uniform_expression_approximation
  intro τ hτ
  refine ⟨normalizedExpression A P hS hN (τ/2) e,fun z => ?_⟩
  exact (regular_ambient_error A P hS hN (half_pos hτ) e z).trans_lt (half_lt_self hτ)

theorem regularAmbient_gram (e : Sector N) (z : ℍ) :
    (regularAmbient A P hS hN e z).adjoint.comp (regularAmbient A P hS hN e z)=
      AsymptoticOrbitDiagonal.corner (AsymptoticCertificateOperators.highStrip P.ε) z := by
  let U := QuantitativeArithmeticRetainedRegularNormalization.normalized A hS hN P
    (multiplier e) (ramifiedParameter e) (by omega : 2≤exponent A P+3) z
  let I := (QuantitativeArithmeticRetainedRegularExtension.TerminalSpace A P z).subtypeL
  have hu : U.adjoint.comp U=1 := (norm_map_iff_adjoint_comp_self U).mp
    (QuantitativeArithmeticRetainedRegularNormalization.normalized_norm A hS hN P
      (multiplier e) (ramifiedParameter e) (fun q _ => multiplier_norm e q)
      (fun p _ => ramifiedParameter_norm e p) (by omega : 2≤exponent A P+3) z
      (regular_contraction A P hS hN e z))
  exact (extended_gram U I hu).trans
    (AsymptoticOrbitRegion.subtype_comp_adjoint (AsymptoticCertificateOperators.highStrip P.ε) z)

theorem regularAmbient_trace_gram (e : Sector N) :
    AsymptoticRegularTrace.trace volume (fun z =>
      (regularAmbient A P hS hN e z).adjoint.comp (regularAmbient A P hS hN e z))=
      ENNReal.ofReal P.ε⁻¹ := by
  simp only [regularAmbient_gram]
  rw [AsymptoticOrbitDiagonal.trace_corner _ (AsymptoticCertificateOperators.highStrip_measurable _)]
  exact AsymptoticHyperbolicArea.closed_terminal_area P.epsilon_pos

variable {ι : Type*}

def expression (τ : ℝ) (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀i,IsCompact (s i)) (d : ℕ) : Expression :=
  observationFilterExpression qs
    (fun i => rowExpression hN (r i) e (hs i) P.epsilon_pos (exponent A P+4))
    (normalizedExpression A P hS hN τ e)
    (fun i => rowBound hN (r i) (hs i) P.epsilon_pos (exponent A P+4)) d

theorem physical_expression (τ : ℝ) (h : ℕ) (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀i,IsCompact (s i)) (d : ℕ) :
    let V := polynomialNormalizedReconstruction
      (physicalScaled A P hS hN (rawTolerance A P τ) (lowerHeight A P τ) e (h+1)) (newtonDepth A P τ)
    holomorphicSum (expression A P hS hN τ e qs r s hs d) (h+1)=
      AsymptoticCylinderLift.lift.toContinuousLinearMap.comp
        ((V.comp ((finiteRowFilter qs
          (fun i => rowOperator hN (r i) e (hs i) P.epsilon_pos (exponent A P+4) (h+1))
          (fun i => rowBound hN (r i) (hs i) P.epsilon_pos (exponent A P+4)) V d).comp V.adjoint)).comp
          AsymptoticCylinderLift.lift.toContinuousLinearMap.adjoint) := by
  dsimp only
  rw [expression,holomorphicSum_observationFilterExpression,physical_normalized]
  let I := AsymptoticCylinderTerminal.ambientLift P.ε
  let J := AsymptoticCylinderLift.lift.toContinuousLinearMap
  let V := polynomialNormalizedReconstruction
    (physicalScaled A P hS hN (rawTolerance A P τ) (lowerHeight A P τ) e (h+1)) (newtonDepth A P τ)
  let L := fun i => holomorphicSum (rowExpression hN (r i) e (hs i) P.epsilon_pos (exponent A P+4)) (h+1)
  let b := fun i => rowBound hN (r i) (hs i) P.epsilon_pos (exponent A P+4)
  have hi := finiteRowFilter_source_transport I (AsymptoticCylinderTerminal.ambientLift_adjoint_self _) (J.comp V) qs L b d
  rw [←comp_assoc]
  apply hi.trans
  rw [finiteRowFilter_target_transport]
  have hr : (fun i => (L i).comp J)=fun i =>
      rowOperator hN (r i) e (hs i) P.epsilon_pos (exponent A P+4) (h+1) := by
    funext i
    exact cylinder_rowExpression hN (r i) e (hs i) _ _ _
  rw [hr]

def regularSourceFilter (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀i,IsCompact (s i)) (d : ℕ) (z : ℍ) :=
  finiteRowFilter qs
    (fun i => AsymptoticRegularObservationRows.row hN (r i) e (hs i) P.epsilon_pos (exponent A P+4) z)
    (fun i => rowBound hN (r i) (hs i) P.epsilon_pos (exponent A P+4)) (regularAmbient A P hS hN e z) d

theorem regularSourceFilter_order (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀i,IsCompact (s i)) (d : ℕ) (z : ℍ) :
    0≤regularSourceFilter A P hS hN e qs r s hs d z ∧
      regularSourceFilter A P hS hN e qs r s hs d z≤1 ∧
      ‖regularSourceFilter A P hS hN e qs r s hs d z‖≤1 :=
  finiteRowFilter_order _ _ _ (fun i => regular_row_norm_le_physical_bound hN (r i) e (hs i) _ _ z)
    _ (regularAmbient_norm A P hS hN e z) d

theorem regularSourceFilter_regular (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀i,IsCompact (s i)) (d : ℕ) :
    (∀g h,Measurable (fun z => matrix (regularSourceFilter A P hS hN e qs r s hs d z) g h)) ∧
      Covariant (regularSourceFilter A P hS hN e qs r s hs d) := by
  apply finiteRowFilter_regular
  · intro i
    simpa only [regularSum_rowExpression] using
      (regularSum_matrix_measurable (rowExpression hN (r i) e (hs i) P.epsilon_pos (exponent A P+4)))
  · intro i
    have he : regularSum (rowExpression hN (r i) e (hs i) P.epsilon_pos (exponent A P+4))=
        fun z => AsymptoticRegularObservationRows.row hN (r i) e (hs i) P.epsilon_pos (exponent A P+4) z :=
      funext (fun z => regularSum_rowExpression hN (r i) e (hs i) _ _ z)
    exact (congrArg Covariant he).mp
      (regularSum_covariant (rowExpression hN (r i) e (hs i) P.epsilon_pos (exponent A P+4)))
  · exact (regularAmbient_regular A P hS hN e).1
  · exact (regularAmbient_regular A P hS hN e).2

section FilterComparison
attribute [local irreducible] normalizedExpression regularSum

private theorem regular_filter_error {ι : Type*} (E : Expression) (rows : ι → Expression)
    (qs : Finset ι) (b : ι → ℝ) (z : ℍ) (U V : RegularSpace →L[ℂ] RegularSpace)
    (L : ι → RegularSpace →L[ℂ] RegularSpace)
    (hE : regularSum E z=V) (hL : (fun i => regularSum (rows i) z)=L)
    (hb : ∀i,‖L i‖≤b i) (hU : ‖U‖≤1) (hV : ‖V‖≤1)
    {τ : ℝ} (he : ‖V-U‖≤τ) (d : ℕ) :
    ‖regularSum (observationFilterExpression qs rows E b d) z-
      U.comp ((finiteRowFilter qs L b U d).comp U.adjoint)‖≤(2*d+2:ℝ)*τ := by
  have hh := (regularSum_observationFilterExpression qs rows E b d z).trans
    (congrArg₂ (fun (R : ι → RegularSpace →L[ℂ] RegularSpace) (W : RegularSpace →L[ℂ] RegularSpace) =>
      W.comp ((finiteRowFilter qs R b W d).comp W.adjoint)) hL hE)
  exact (congrArg (fun R : RegularSpace →L[ℂ] RegularSpace =>
    ‖R-U.comp ((finiteRowFilter qs L b U d).comp U.adjoint)‖) hh).trans_le
    ((finiteRowFilter_sandwich_difference qs L b hb U V hU hV d).trans
      (mul_le_mul_of_nonneg_left he (by positivity)))

set_option backward.isDefEq.respectTransparency true in
theorem regular_expression_error {τ : ℝ} (hτ : 0<τ) (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀i,IsCompact (s i)) (d : ℕ) (z : ℍ) :
    ‖regularSum (expression A P hS hN τ e qs r s hs d) z-
      (regularAmbient A P hS hN e z).comp
        ((regularSourceFilter A P hS hN e qs r s hs d z).comp (regularAmbient A P hS hN e z).adjoint)‖≤
      (2*d+2:ℝ)*τ := by
  let W := polynomialNormalizedReconstruction
    (regularScaled A P hS hN (rawTolerance A P τ) (lowerHeight A P τ) e z) (newtonDepth A P τ)
  let I := (QuantitativeArithmeticRetainedRegularExtension.TerminalSpace A P z).subtypeL
  let V : RegularSpace →L[ℂ] RegularSpace := W.comp I.adjoint
  have hn : ‖W‖≤1 := polynomialNormalizedReconstruction_norm_le _
    (regularScaled_norm A P hS hN (rawTolerance A P τ) (lowerHeight A P τ) e z) (newtonDepth A P τ)
  have hi : ‖I.adjoint‖≤1 := subtype_adjoint_bound _
  have hv : ‖V‖≤1 := (opNorm_comp_le W I.adjoint).trans
    ((mul_le_mul hn hi (norm_nonneg I.adjoint) zero_le_one).trans_eq (one_mul _))
  have hEval : regularSum (normalizedExpression A P hS hN τ e) z=V := regular_normalized A P hS hN τ e z
  have hdiff : ‖V-regularAmbient A P hS hN e z‖≤τ :=
    (congrArg (fun R : RegularSpace →L[ℂ] RegularSpace => ‖R-regularAmbient A P hS hN e z‖) hEval).symm.trans_le
      (regular_ambient_error A P hS hN hτ e z)
  exact regular_filter_error (normalizedExpression A P hS hN τ e)
    (fun i => rowExpression hN (r i) e (hs i) P.epsilon_pos (exponent A P+4)) qs
    (fun i => rowBound hN (r i) (hs i) P.epsilon_pos (exponent A P+4)) z
    (regularAmbient A P hS hN e z) V
    (fun i => AsymptoticRegularObservationRows.row hN (r i) e (hs i) P.epsilon_pos (exponent A P+4) z)
    hEval (funext (fun i => regularSum_rowExpression hN (r i) e (hs i) _ _ z))
    (fun i => regular_row_norm_le_physical_bound hN (r i) e (hs i) _ _ z)
    (regularAmbient_norm A P hS hN e z) hv hdiff d

end FilterComparison

/-- Quantitative row representatives preserve the operator while making
all integer matrix sizes explicit. -/
def quantified (τ : ℝ) (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀i,IsCompact (s i)) {L H : ℝ} (hL : 0<L)
    (hre : ∀i z,z∈s i → |z.re|≤1) (hlo : ∀i z,z∈s i → L≤z.im)
    (hhi : ∀i z,z∈s i → z.im≤H) (d : ℕ) : Expression :=
  observationFilterExpression qs
    (fun i => quantifiedRowExpression hN (r i) e (hs i) hL P.epsilon_pos
      (hre i) (hlo i) (hhi i) (exponent A P+4))
    (normalizedExpression A P hS hN τ e)
    (fun i => rowBound hN (r i) (hs i) P.epsilon_pos (exponent A P+4)) d

theorem quantified_physical (τ : ℝ) (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀i,IsCompact (s i)) {L H : ℝ} (hL : 0<L)
    (hre : ∀i z,z∈s i → |z.re|≤1) (hlo : ∀i z,z∈s i → L≤z.im)
    (hhi : ∀i z,z∈s i → z.im≤H) (d m : ℕ) :
    holomorphicSum (quantified A P hS hN τ e qs r s hs hL hre hlo hhi d) m=
      holomorphicSum (expression A P hS hN τ e qs r s hs d) m := by
  rw [quantified,expression,holomorphicSum_observationFilterExpression,holomorphicSum_observationFilterExpression]
  have he : (fun i => holomorphicSum (quantifiedRowExpression hN (r i) e (hs i) hL P.epsilon_pos
      (hre i) (hlo i) (hhi i) (exponent A P+4)) m)=
      fun i => holomorphicSum (rowExpression hN (r i) e (hs i) P.epsilon_pos (exponent A P+4)) m := by
    funext i
    exact (quantifiedRowExpression_spec hN (r i) e (hs i) hL _ (hre i) (hlo i) (hhi i) _).1 m
  rw [he]

theorem quantified_regular (τ : ℝ) (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀i,IsCompact (s i)) {L H : ℝ} (hL : 0<L)
    (hre : ∀i z,z∈s i → |z.re|≤1) (hlo : ∀i z,z∈s i → L≤z.im)
    (hhi : ∀i z,z∈s i → z.im≤H) (d : ℕ) (z : ℍ) :
    regularSum (quantified A P hS hN τ e qs r s hs hL hre hlo hhi d) z=
      regularSum (expression A P hS hN τ e qs r s hs d) z := by
  rw [quantified,expression,regularSum_observationFilterExpression,regularSum_observationFilterExpression]
  have he : (fun i => regularSum (quantifiedRowExpression hN (r i) e (hs i) hL P.epsilon_pos
      (hre i) (hlo i) (hhi i) (exponent A P+4)) z)=
      fun i => regularSum (rowExpression hN (r i) e (hs i) P.epsilon_pos (exponent A P+4)) z := by
    funext i
    exact (quantifiedRowExpression_spec hN (r i) e (hs i) hL _ (hre i) (hlo i) (hhi i) _).2.1 z
  rw [he]

/-- The full mixed filter inherits explicit matrix height directly from
its reconstruction and row bounds; row cardinality only affects expansion cost. -/
theorem quantified_matrix_bound (τ : ℝ) (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀i,IsCompact (s i)) {L H : ℝ} (hL : 0<L)
    (hre : ∀i z,z∈s i → |z.re|≤1) (hlo : ∀i z,z∈s i → L≤z.im)
    (hhi : ∀i z,z∈s i → z.im≤H) {R B : ℝ} (hR : 0≤R) (hB : 0≤B)
    (hr : ∀i∈qs,quantifiedRowHeight hN (r i) L H≤R)
    (hb : ExpressionMatrixBound (normalizedExpression A P hS hN τ e) B) (d : ℕ) :
    ExpressionMatrixBound (quantified A P hS hN τ e qs r s hs hL hre hlo hhi d)
      (4*B^2*(2*max 1 (8*R^2*B^2))^d) := by
  apply expressionMatrixBound_observationFilter _ _ _ _ hR hB _ hb d
  intro i hi
  exact ((quantifiedRowExpression_spec hN (r i) e (hs i) hL _ (hre i) (hlo i) (hhi i) _).2.2.2.2).mono (hr i hi)

theorem quantified_complexity (τ : ℝ) (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀i,IsCompact (s i)) {L H : ℝ} (hL : 0<L)
    (hre : ∀i z,z∈s i → |z.re|≤1) (hlo : ∀i z,z∈s i → L≤z.im)
    (hhi : ∀i z,z∈s i → z.im≤H) (d : ℕ) :
    let V := normalizedExpression A P hS hN τ e
    let E := quantified A P hS hN τ e qs r s hs hL hre hlo hhi d
    expressionBound E≤expressionBound V^2*
      (1+∑i∈qs,(quantifiedRowMass hN (r i) L H (exponent A P+4)*expressionBound V)^2)^d ∧
    E.length≤V.length^2*(1+∑i∈qs,(quantifiedRowLength hN (r i) L H*V.length)^2)^d := by
  apply observationFilterExpression_complexity_le _ _ _ _ _ _ le_rfl le_rfl
  · intro i _
    exact (quantifiedRowExpression_spec hN (r i) e (hs i) hL _ (hre i) (hlo i) (hhi i) _).2.2.2.1
  · intro i _
    exact (quantifiedRowExpression_spec hN (r i) e (hs i) hL _ (hre i) (hlo i) (hhi i) _).2.2.1.le

/-- Cyclicity moves the full regular sandwich to its finite terminal
source; the terminal area and all measurability hypotheses are proved above. -/
theorem source_trace (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀i,IsCompact (s i)) (d : ℕ) :
    signedTrace volume (fun z => (regularAmbient A P hS hN e z).comp
      ((regularSourceFilter A P hS hN e qs r s hs d z).comp (regularAmbient A P hS hN e z).adjoint))=
    signedTrace volume (fun z => (regularSourceFilter A P hS hN e qs r s hs d z).comp
      (AsymptoticOrbitDiagonal.corner (AsymptoticCertificateOperators.highStrip P.ε) z)) := by
  have hf : AsymptoticRegularTrace.trace volume (fun z =>
      (regularAmbient A P hS hN e z).adjoint.comp (regularAmbient A P hS hN e z))<∞ := by
    rw [regularAmbient_trace_gram]
    exact ENNReal.ofReal_lt_top
  have ht := signedTrace_sandwich volume AsymptoticRationalGroup.measurePreserving
    (regularAmbient A P hS hN e) (regularSourceFilter A P hS hN e qs r s hs d)
    (regularAmbient_regular A P hS hN e).1 (regularSourceFilter_regular A P hS hN e qs r s hs d).1
    (regularAmbient_regular A P hS hN e).2 (regularSourceFilter_regular A P hS hN e qs r s hs d).2
    hf (fun z => (regularSourceFilter_order A P hS hN e qs r s hs d z).2.2)
  simpa only [regularAmbient_gram] using ht

#print axioms source_trace

#print axioms quantified_physical
#print axioms quantified_regular
#print axioms quantified_matrix_bound
#print axioms quantified_complexity

#print axioms regularAmbient_norm
#print axioms regularAmbient_regular
#print axioms regularAmbient_gram
#print axioms regularAmbient_trace_gram
#print axioms physical_expression
#print axioms regularSourceFilter_order
#print axioms regularSourceFilter_regular
#print axioms regular_expression_error
end QuantitativeArithmeticRetainedFilterExpression
