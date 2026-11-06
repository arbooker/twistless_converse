module

public import QuantitativeArithmeticRetainedFilterExpressionV1
public import QuantitativeArithmeticRetainedTraceCutoffV1
public import QuantitativeHolomorphicTerminalTraceAlgebraV1
public import QuantitativeHolomorphicFilterComparisonV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedGeometricTrace
open UpperHalfPlane ContinuousLinearMap MeasureTheory AsymptoticSectorSigns
open AsymptoticFiniteBranch AsymptoticCompactObservationCount AsymptoticRegularTrace
open AsymptoticCylinder AsymptoticCylinderModeComparison AsymptoticUnweightedKernel
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedPreparedReconstruction
open QuantitativeArithmeticRetainedFiniteTransport
open QuantitativeArithmeticRetainedFiniteNormalization
open QuantitativeArithmeticRetainedFilterExpression QuantitativeArithmeticRetainedTraceCutoff
open QuantitativeHolomorphic AsymptoticFourierNorm
open scoped ENNReal

private theorem sandwich_norm {G H : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : G →L[ℂ] H) (F : G →L[ℂ] G) (hV : ‖V‖≤1) (hF : ‖F‖≤1) :
    ‖V.comp (F.comp V.adjoint)‖≤1 := by
  have ha : ‖V.adjoint‖≤1 := by rwa [adjoint.norm_map]
  have hi : ‖F.comp V.adjoint‖≤1 := (opNorm_comp_le _ _).trans
    ((mul_le_mul hF ha (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  exact (opNorm_comp_le _ _).trans
    ((mul_le_mul hV hi (norm_nonneg _) zero_le_one).trans_eq (one_mul _))

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ)
    (P : Parameters A) (hS : ∀p∈S,p.Prime) (hN : 0<N) {ι : Type*}

def regularFilter (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀i,IsCompact (s i)) (d : ℕ) (z : ℍ) :=
  (regularAmbient A P hS hN e z).comp
    ((QuantitativeArithmeticRetainedFilterExpression.regularSourceFilter A P hS hN e qs r s hs d z).comp
      (regularAmbient A P hS hN e z).adjoint)

theorem regularFilter_norm (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀i,IsCompact (s i)) (d : ℕ) (z : ℍ) :
    ‖regularFilter A P hS hN e qs r s hs d z‖≤1 :=
  sandwich_norm _ _ (regularAmbient_norm A P hS hN e z)
    (QuantitativeArithmeticRetainedFilterExpression.regularSourceFilter_order A P hS hN e qs r s hs d z).2.2

theorem regularFilter_measurable (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀i,IsCompact (s i)) (d : ℕ) :
    ∀g h,Measurable (fun z => matrix (regularFilter A P hS hN e qs r s hs d z) g h) := by
  have hu := (regularAmbient_regular A P hS hN e).1
  have hf := (QuantitativeArithmeticRetainedFilterExpression.regularSourceFilter_regular A P hS hN e qs r s hs d).1
  exact matrix_comp_measurable _ _ hu (matrix_comp_measurable _ _ hf (matrix_adjoint_measurable _ hu))

theorem regularFilter_positive (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀i,IsCompact (s i)) (d : ℕ) (z : ℍ) :
    (regularFilter A P hS hN e qs r s hs d z).IsPositive := by
  have hp := nonneg_iff_isPositive.mp
    (QuantitativeArithmeticRetainedFilterExpression.regularSourceFilter_order A P hS hN e qs r s hs d z).1
  simpa only [regularFilter,adjoint_adjoint,comp_assoc] using hp.adjoint_conj (regularAmbient A P hS hN e z).adjoint

theorem regularFilter_trace_finite (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀i,IsCompact (s i)) (d : ℕ) :
    AsymptoticRegularTrace.trace volume (regularFilter A P hS hN e qs r s hs d)<∞ := by
  have hu := regularAmbient_regular A P hS hN e
  have he := rational_trace_adjoint_mul (regularAmbient A P hS hN e) hu.1 hu.2
  have ht := trace_sandwich_le_range_gram volume (regularAmbient A P hS hN e)
    (QuantitativeArithmeticRetainedFilterExpression.regularSourceFilter A P hS hN e qs r s hs d)
    (fun z => (QuantitativeArithmeticRetainedFilterExpression.regularSourceFilter_order A P hS hN e qs r s hs d z).2.2)
  apply ht.trans_lt
  rw [←he,regularAmbient_trace_gram]
  exact ENNReal.ofReal_lt_top

theorem retained_le_source (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀i,IsCompact (s i)) (d : ℕ) (Y H : ℝ) :
    signedTrace volume (regularRetained Y H (regularFilter A P hS hN e qs r s hs d))≤
      signedTrace volume (fun z =>
        (QuantitativeArithmeticRetainedFilterExpression.regularSourceFilter A P hS hN e qs r s hs d z).comp
          (AsymptoticOrbitDiagonal.corner (AsymptoticCertificateOperators.highStrip P.ε) z)) :=
  (regularRetained_trace_le_full Y H _ (regularFilter_measurable A P hS hN e qs r s hs d)
    (regularFilter_positive A P hS hN e qs r s hs d)
    (regularFilter_trace_finite A P hS hN e qs r s hs d)).trans_eq
    (source_trace A P hS hN e qs r s hs d)

theorem finite_retained_error {τ Y : ℝ} (hτ : 0<τ) (hY : 0<Y) (H : ℝ)
    (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀i,IsCompact (s i)) (d : ℕ) :
    ‖signedTrace volume (regularRetained Y H (regularSum (expression A P hS hN τ e qs r s hs d)))-
      signedTrace volume (regularRetained Y H (regularFilter A P hS hN e qs r s hs d))‖≤(2*d+2:ℝ)*τ/Y :=
  regularRetained_trace_difference hY H _ _
    (regularSum_matrix_measurable _) (regularFilter_measurable A P hS hN e qs r s hs d)
    (regularSum_norm_le _) (regularFilter_norm A P hS hN e qs r s hs d)
    (regular_expression_error A P hS hN hτ e qs r s hs d)

theorem cylinderFilter_norm (δ Y : ℝ) (h : ℕ) (e : Sector N) (n : ℕ) (qs : Finset ι)
    (r : ι → Row N) (s : ι → Set ℍ) (hs : ∀i,IsCompact (s i)) (d : ℕ) :
    ‖cylinderFilter A hS hN P δ Y h e n qs r s hs d‖≤1 := by
  let V := polynomialNormalizedReconstruction (physicalScaled A P hS hN δ Y e (h+1)) n
  have hv : ‖V‖≤1 := polynomialNormalizedReconstruction_norm_le _ (physicalScaled_norm A P hS hN δ Y e (h+1)) n
  exact sandwich_norm V _ hv (finiteRowFilter_order _ _ _
    (fun i => rowOperator_norm_le hN (r i) e (hs i) P.epsilon_pos (exponent A P+4) (h+1)) V hv d).2.2

section TerminalComparison
attribute [local irreducible] normalizedExpression regularSum

/-- The finite normalizer has the same fixed terminal source as its limit. -/
def finiteAmbient (τ : ℝ) (e : Sector N) := regularSum (normalizedExpression A P hS hN τ e)

set_option backward.isDefEq.respectTransparency true in
theorem finiteAmbient_norm (τ : ℝ) (e : Sector N) (z : ℍ) :
    ‖finiteAmbient A P hS hN τ e z‖≤1 := by
  have he := regular_normalized A P hS hN τ e z
  have hv := polynomialNormalizedReconstruction_norm_le _
    (regularScaled_norm A P hS hN (rawTolerance A P τ) (lowerHeight A P τ) e z) (newtonDepth A P τ)
  have hi : ‖(QuantitativeArithmeticRetainedRegularExtension.TerminalSpace A P z).subtypeL.adjoint‖≤1 := by
    rw [adjoint.norm_map]
    apply opNorm_le_bound _ zero_le_one
    intro v
    simp
  change ‖regularSum (normalizedExpression A P hS hN τ e) z‖≤1
  rw [he]
  exact (opNorm_comp_le _ _).trans ((mul_le_mul hv hi (norm_nonneg _) zero_le_one).trans_eq (one_mul _))

set_option backward.isDefEq.respectTransparency true in
theorem finiteAmbient_terminal (τ : ℝ) (e : Sector N) (z : ℍ) :
    (finiteAmbient A P hS hN τ e z).comp
      (AsymptoticOrbitDiagonal.corner (AsymptoticCertificateOperators.highStrip P.ε) z)=
      finiteAmbient A P hS hN τ e z := by
  let I := (QuantitativeArithmeticRetainedRegularExtension.TerminalSpace A P z).subtypeL
  have hi : I.adjoint.comp I=1 :=
    AsymptoticOrbitRegion.adjoint_comp_subtype (G := AsymptoticRationalGroup.Group) _ z
  have hp : I.comp I.adjoint=AsymptoticOrbitDiagonal.corner (AsymptoticCertificateOperators.highStrip P.ε) z :=
    AsymptoticOrbitRegion.subtype_comp_adjoint _ z
  let V := polynomialNormalizedReconstruction
    (regularScaled A P hS hN (rawTolerance A P τ) (lowerHeight A P τ) e z) (newtonDepth A P τ)
  have he : finiteAmbient A P hS hN τ e z=V.comp I.adjoint := regular_normalized A P hS hN τ e z
  calc
    _ = (V.comp I.adjoint).comp (I.comp I.adjoint) := congrArg₂ (fun X Z => X.comp Z) he hp.symm
    _ = V.comp I.adjoint := by
      ext1 v
      have hv := congrArg (fun W => W (I.adjoint v)) hi
      change I.adjoint (I (I.adjoint v))=I.adjoint v at hv
      change V (I.adjoint (I (I.adjoint v)))=V (I.adjoint v)
      exact congrArg V hv
    _ = _ := he.symm

theorem finiteAmbient_trace_finite (τ : ℝ) (e : Sector N) :
    AsymptoticRegularTrace.trace volume (fun z =>
      (finiteAmbient A P hS hN τ e z).adjoint.comp (finiteAmbient A P hS hN τ e z))<∞ := by
  apply AsymptoticHyperbolicArea.closed_terminal_trace_finite (C:=1) P.epsilon_pos
  · intro z
    exact contraction_gram_norm_le _ (finiteAmbient_norm A P hS hN τ e z)
  · intro z
    rw [comp_assoc]
    exact congrArg (fun W => (finiteAmbient A P hS hN τ e z).adjoint.comp W)
      (finiteAmbient_terminal A P hS hN τ e z)

set_option backward.isDefEq.respectTransparency true in
theorem fixed_source_error {τ : ℝ} (hτ : 0<τ) (Y H : ℝ)
    (e : Sector N) (qs : Finset ι) (r : ι → Row N) (s : ι → Set ℍ)
    (hs : ∀i,IsCompact (s i)) (d : ℕ) :
    signedTrace volume (regularRetained Y H
      (regularSum (expression A P hS hN τ e qs r s hs d)))≤
    signedTrace volume (fun z =>
      (QuantitativeArithmeticRetainedFilterExpression.regularSourceFilter A P hS hN e qs r s hs d z).comp
        (AsymptoticOrbitDiagonal.corner (AsymptoticCertificateOperators.highStrip P.ε) z))+
      (2*d+2:ℝ)*τ/P.ε := by
  let rows := fun i => rowExpression hN (r i) e (hs i) P.epsilon_pos (exponent A P+4)
  let L := fun i z => regularSum (rows i) z
  let b := fun i => rowBound hN (r i) (hs i) P.epsilon_pos (exponent A P+4)
  let U := regularAmbient A P hS hN e
  let V := finiteAmbient A P hS hN τ e
  let FU := fun z => finiteRowFilter qs (fun i => L i z) b (U z) d
  let FV := fun z => finiteRowFilter qs (fun i => L i z) b (V z) d
  let GU := fun z => (U z).adjoint.comp (U z)
  let GV := fun z => (V z).adjoint.comp (V z)
  let CU := fun z => (FU z).comp (GU z)
  let CV := fun z => (FV z).comp (GV z)
  let E := expression A P hS hN τ e qs r s hs d
  have hL (i : ι) (z : UpperHalfPlane) : ‖L i z‖≤b i := by
    dsimp only [L,rows,b]
    rw [regularSum_rowExpression]
    exact regular_row_norm_le_physical_bound hN (r i) e (hs i) P.epsilon_pos (exponent A P+4) z
  have hU := regularAmbient_norm A P hS hN e
  have hV := finiteAmbient_norm A P hS hN τ e
  have hFU (z : UpperHalfPlane) : ‖FU z‖≤1 :=
    (finiteRowFilter_order qs (fun i => L i z) b (fun i => hL i z) (U z) (hU z) d).2.2
  have hFV (z : UpperHalfPlane) : ‖FV z‖≤1 :=
    (finiteRowFilter_order qs (fun i => L i z) b (fun i => hL i z) (V z) (hV z) d).2.2
  have hmV := regularSum_matrix_measurable
    (normalizedExpression A P hS hN τ e)
  have hcV := regularSum_covariant
    (normalizedExpression A P hS hN τ e)
  have hrU := regularAmbient_regular A P hS hN e
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
      (AsymptoticCertificateOperators.highStrip P.ε) z :=
    regularAmbient_gram A P hS hN e z
  have hsU (z : UpperHalfPlane) : (CU z).comp (AsymptoticOrbitDiagonal.corner
      (AsymptoticCertificateOperators.highStrip P.ε) z)=CU z := by
    dsimp only [CU]
    rw [hGU,comp_assoc,AsymptoticOrbitDiagonal.corner_idempotent]
  have hsV (z : UpperHalfPlane) : (CV z).comp (AsymptoticOrbitDiagonal.corner
      (AsymptoticCertificateOperators.highStrip P.ε) z)=CV z := by
    dsimp only [CV,GV]
    rw [comp_assoc,comp_assoc,finiteAmbient_terminal]
  have hd (z : UpperHalfPlane) : ‖CV z-CU z‖≤((2*d+2:ℝ)*τ) :=
    (finiteRowFilter_sourceProduct_difference qs (fun i => L i z) b (fun i => hL i z)
      (U z) (V z) (hU z) (hV z) d).trans
        (mul_le_mul_of_nonneg_left (regular_ambient_error A P hS hN hτ e z) (by positivity))
  have harea : volume (AsymptoticCertificateOperators.highStrip P.ε)=ENNReal.ofReal P.ε⁻¹ :=
    AsymptoticHyperbolicArea.closed_terminal_area P.epsilon_pos
  have hfinite : volume (AsymptoticCertificateOperators.highStrip P.ε)<∞ := by
    rw [harea]
    exact ENNReal.ofReal_lt_top
  have hdiff := norm_signedTrace_sub_le_corner volume
    (AsymptoticCertificateOperators.highStrip_measurable P.ε) hfinite CV CU
    (hmCV 1 1) (hmCU 1 1) hCV hCU hsV hsU hd
  rw [harea,ENNReal.toReal_ofReal (inv_nonneg.mpr P.epsilon_pos.le),←div_eq_mul_inv] at hdiff
  have he (z : UpperHalfPlane) : regularSum E z=(V z).comp ((FV z).comp (V z).adjoint) := by
    exact regularSum_observationFilterExpression qs rows
      (normalizedExpression A P hS hN τ e) b d z
  have hf := finiteAmbient_trace_finite A P hS hN τ e
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
  have hsource : CU=fun z => (QuantitativeArithmeticRetainedFilterExpression.regularSourceFilter A P hS hN e qs r s hs d z).comp
      (AsymptoticOrbitDiagonal.corner (AsymptoticCertificateOperators.highStrip P.ε) z) := by
    funext z
    have hfilter : FU z=QuantitativeArithmeticRetainedFilterExpression.regularSourceFilter A P hS hN e qs r s hs d z := by
      dsimp only [FU,L,rows,U,b,QuantitativeArithmeticRetainedFilterExpression.regularSourceFilter]
      simp only [regularSum_rowExpression]
    exact congrArg₂ (fun X Z : RegularSpace →L[ℂ] RegularSpace => X.comp Z) hfilter (hGU z)
  have habdiff : |signedTrace volume CV-signedTrace volume CU| ≤
      ((2*d+2:ℝ)*τ)/P.ε := by
    simpa only [Real.norm_eq_abs] using hdiff
  have hsourceTrace := congrArg (signedTrace volume) hsource
  change signedTrace volume (regularRetained Y H (regularSum E)) ≤ _
  linarith only [hret,hfull,hsourceTrace,habdiff,
    le_abs_self (signedTrace volume CV-signedTrace volume CU)]

end TerminalComparison

/-- The finite mixed reconstruction gives the actual retained cylinder trace. -/
theorem retained_lift (τ H : ℝ) (h : ℕ) (e : Sector N) (qs : Finset ι)
    (r : ι → Row N) (s : ι → Set ℍ) (hs : ∀i,IsCompact (s i)) (d : ℕ) :
    liftedTrace h P.epsilon_pos
      (holomorphicSum (retainedExpression (lowerHeight A P τ) H
        (expression A P hS hN τ e qs r s hs d)) (h+1)) =
      retainedTrace A hS hN P (rawTolerance A P τ) (lowerHeight A P τ) H h e
        (newtonDepth A P τ) qs r s hs d 0 := by
  rw [holomorphicSum_retainedExpression,holomorphic_corner,physical_expression]
  exact retained_lift_trace h P.epsilon_pos (lowerHeight A P τ) H _

/-- Weighted Fourier modes and finite rational branch geometry compare the
actual finite mixed reconstruction with its retained regular counterpart. -/
theorem geometric_comparison {τ : ℝ} (hτ : 0<τ) (H D : ℝ) (hH : 0<H) (hD : 0≤D)
    (h : ℕ) (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀i,IsCompact (s i)) (d : ℕ) (E : Expression)
    (hphysical : holomorphicSum E (h+1)=holomorphicSum (expression A P hS hN τ e qs r s hs d) (h+1))
    (_hregular : regularSum E=regularSum (expression A P hS hN τ e qs r s hs d)) (Z : Finset ℤ)
    (hsmall : (h+1:ℝ)^(-(1/3:ℝ))*D≤1)
    (hfar : ∀a : ℤ,a∉Z → 2*compactBaseBound (lowerHeight A P τ) H 1≤1+|(a:ℝ)|)
    (geom : ∀b∈E,b.label≠1 →
      RetainedBranchGeometry b (lowerHeight A P τ) H D Z) :
    let Y := lowerHeight A P τ
    |retainedTrace A hS hN P (rawTolerance A P τ) Y H h e (newtonDepth A P τ)
        qs r s hs d (exponent A P+4)/(2*h+2:ℝ)-
      signedTrace volume (regularRetained Y H (regularSum E))/(4*Real.pi)| ≤
      (2*Real.sqrt (localizedErrorBound (exponent A P+4) (4*Real.pi) Y)*
        Real.sqrt (massSlope (exponent A P+4) (4*Real.pi) Y))*(Real.sqrt (2*h+2:ℝ))⁻¹+
      (expressionBound E+(E.length:ℝ))*uniformRetainedTraceError D Y H h Z.card := by
  dsimp only
  have hy := lowerHeight_pos A P hτ
  have hw := retained_weighted_trace_difference (2*h) (exponent A P+4) P.epsilon_pos hy H
    (cylinderFilter A hS hN P (rawTolerance A P τ) (lowerHeight A P τ) h e
      (newtonDepth A P τ) qs r s hs d)
    (cylinderFilter_norm A P hS hN _ _ h e _ qs r s hs d)
  have hb := retained_expression_uniform_trace_bound E
    P.epsilon_pos hD hy hH h hsmall Z hfar geom
  have hret : holomorphicSum (retainedExpression (lowerHeight A P τ) H E) (h+1)=
      holomorphicSum (retainedExpression (lowerHeight A P τ) H
        (expression A P hS hN τ e qs r s hs d)) (h+1) := by
    simp only [holomorphicSum_retainedExpression,hphysical]
  rw [hret,retained_lift] at hb
  have hre : regularSum (retainedExpression (lowerHeight A P τ) H E)=
      regularRetained (lowerHeight A P τ) H (regularSum E) := by
    funext z
    exact regularSum_retainedExpression _ _ _ z
  rw [hre] at hb
  have hw' := hw
  simp only [Real.norm_eq_abs,sub_div,Nat.cast_mul,Nat.cast_ofNat] at hw'
  apply (abs_sub_le _ (retainedTrace A hS hN P (rawTolerance A P τ) (lowerHeight A P τ) H h e
    (newtonDepth A P τ) qs r s hs d 0/(2*h+2:ℝ)) _).trans
  apply add_le_add hw'
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hb

/-- Closing the regular side uses positivity and the fixed terminal source;
no regular trace estimate is assumed. -/
theorem retained_source_bound {τ : ℝ} (hτ : 0<τ) (H D : ℝ) (hH : 0<H) (hD : 0≤D)
    (h : ℕ) (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀i,IsCompact (s i)) (d : ℕ) (E : Expression)
    (hphysical : holomorphicSum E (h+1)=holomorphicSum (expression A P hS hN τ e qs r s hs d) (h+1))
    (hregular : regularSum E=regularSum (expression A P hS hN τ e qs r s hs d)) (Z : Finset ℤ)
    (hsmall : (h+1:ℝ)^(-(1/3:ℝ))*D≤1)
    (hfar : ∀a : ℤ,a∉Z → 2*compactBaseBound (lowerHeight A P τ) H 1≤1+|(a:ℝ)|)
    (geom : ∀b∈E,b.label≠1 →
      RetainedBranchGeometry b (lowerHeight A P τ) H D Z) :
    let Y := lowerHeight A P τ
    retainedTrace A hS hN P (rawTolerance A P τ) Y H h e (newtonDepth A P τ)
        qs r s hs d (exponent A P+4)/(2*h+2:ℝ) ≤
      signedTrace volume (fun z =>
        (QuantitativeArithmeticRetainedFilterExpression.regularSourceFilter A P hS hN e qs r s hs d z).comp
          (AsymptoticOrbitDiagonal.corner (AsymptoticCertificateOperators.highStrip P.ε) z))/(4*Real.pi)+
      (2*Real.sqrt (localizedErrorBound (exponent A P+4) (4*Real.pi) Y)*
        Real.sqrt (massSlope (exponent A P+4) (4*Real.pi) Y))*(Real.sqrt (2*h+2:ℝ))⁻¹+
      (expressionBound E+(E.length:ℝ))*uniformRetainedTraceError D Y H h Z.card+
      ((2*d+2:ℝ)*τ/P.ε)/(4*Real.pi) := by
  dsimp only
  have hg := (abs_le.mp (geometric_comparison A P hS hN hτ H D hH hD h e qs r s hs d E hphysical hregular Z hsmall hfar geom)).2
  have hsour := fixed_source_error A P hS hN hτ (lowerHeight A P τ) H e qs r s hs d
  rw [←hregular] at hsour
  have hd := div_le_div_of_nonneg_right hsour (by positivity : 0≤4*Real.pi)
  rw [add_div] at hd
  linarith

private theorem trace_chain (a b c T E F x : ℝ) (hx : 0<x)
    (hE : 0≤E) (_hstep : 0≤2*x-2)
    (hab : |b-a|/(2*x-2)≤E) (hbc : |b-c|/x≤F) (hc : c/x≤T)
    (hden : 0<2*x-2) : a/x≤T+2*E+F := by
  have h1 := (div_le_iff₀ hden).mp hab
  have h2 := (div_le_iff₀ hx).mp hbc
  have h3 := (div_le_iff₀ hx).mp hc
  have h4 := neg_le_abs (b-a)
  have h5 := le_abs_self (b-c)
  apply (div_le_iff₀ hx).mpr
  nlinarith

/-- Complete mixed sector comparison before choosing scalar schedules.
All operator and trace estimates have been discharged; the remaining inputs
are explicit numerical error bounds and finite integer matrix geometry. -/
theorem sector_le_source (hdiv : ∀p∈S,p∣Q) (hbad : ∀p∈S,p∣N)
    {τ : ℝ} (hτ : 0<τ) (H D : ℝ) (hH : 0<H) (hD : 0≤D)
    (h : ℕ) (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀i,IsCompact (s i)) (d : ℕ) (E : Expression)
    (hphysical : holomorphicSum E (h+1)=holomorphicSum (expression A P hS hN τ e qs r s hs d) (h+1))
    (hregular : regularSum E=regularSum (expression A P hS hN τ e qs r s hs d)) (Z : Finset ℤ)
    (herr0 : 0<QuantitativeArithmeticRetainedFilterTrace.traceError A P
      (rawTolerance A P τ) (lowerHeight A P τ) (newtonDepth A P τ) d)
    (herr1 : QuantitativeArithmeticRetainedFilterTrace.traceError A P
      (rawTolerance A P τ) (lowerHeight A P τ) (newtonDepth A P τ) d≤1)
    (hsmall : (h+1:ℝ)^(-(1/3:ℝ))*D≤1)
    (hfar : ∀a : ℤ,a∉Z → 2*compactBaseBound (lowerHeight A P τ) H 1≤1+|(a:ℝ)|)
    (geom : ∀b∈E,b.label≠1 →
      RetainedBranchGeometry b (lowerHeight A P τ) H D Z) :
    let Y := lowerHeight A P τ
    let n := newtonDepth A P τ
    let t := exponent A P+4
    let B := (3/2:ℝ)^n
    let C := QuantitativeArithmeticRetainedFilterTrace.traceMajorant A P n
    (Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P.s) e):ℝ)/(2*h+2:ℝ)≤
      signedTrace volume (fun z =>
        (QuantitativeArithmeticRetainedFilterExpression.regularSourceFilter A P hS hN e qs r s hs d z).comp
          (AsymptoticOrbitDiagonal.corner (AsymptoticCertificateOperators.highStrip P.ε) z))/(4*Real.pi)+
      (2*Real.sqrt (localizedErrorBound t (4*Real.pi) Y)*Real.sqrt (massSlope t (4*Real.pi) Y))*
        (Real.sqrt (2*h+2:ℝ))⁻¹+
      (expressionBound E+(E.length:ℝ))*uniformRetainedTraceError D Y H h Z.card+
      ((2*d+2:ℝ)*τ/P.ε)/(4*Real.pi)+
      2*((2+2*C*majorantConstant t (4*Real.pi) P.ε)*Real.sqrt
        (QuantitativeArithmeticRetainedFilterTrace.traceError A P (rawTolerance A P τ) Y n d))+
      upperCutError (B^2*(1+majorantConstant t (4*Real.pi) P.ε)) B 1
        (massBound (2*h) t (4*Real.pi) H/(2*h+2:ℝ)) := by
  dsimp only
  have hs0 := QuantitativeArithmeticRetainedFilterTrace.sector_finrank_le_trace A hS hN P hdiv hbad h e qs r s hs d
  have hf := QuantitativeArithmeticRetainedFilterTrace.finite_trace_error A hS hN P
    (rawTolerance_pos A P hτ) (lowerHeight_pos A P hτ).le h e (newtonDepth A P τ) qs r s hs d herr0 herr1
  have hu := upper_cut_error A hS hN P (rawTolerance A P τ) (lowerHeight A P τ) H hH h e
    (newtonDepth A P τ) qs r s hs d
  have hg := retained_source_bound A P hS hN hτ H D hH hD h e qs r s hs d E hphysical hregular Z hsmall hfar geom
  have he0 : 0≤(2+2*QuantitativeArithmeticRetainedFilterTrace.traceMajorant A P (newtonDepth A P τ)*
      majorantConstant (exponent A P+4) (4*Real.pi) P.ε)*Real.sqrt
        (QuantitativeArithmeticRetainedFilterTrace.traceError A P (rawTolerance A P τ)
          (lowerHeight A P τ) (newtonDepth A P τ) d) :=
    (div_nonneg (norm_nonneg _) (by positivity)).trans hf
  simp only [Real.norm_eq_abs] at hf hu
  have hf' := hf
  have hden : 2*(2*(h:ℝ)+2)-2=4*(h:ℝ)+2 := by ring
  rw [←hden] at hf'
  have hc := trace_chain _ _ _ _ _ _ (2*(h:ℝ)+2) (by positivity) he0 (by nlinarith [Nat.cast_nonneg (α:=ℝ) h])
    hf' hu hg (by nlinarith [Nat.cast_nonneg (α:=ℝ) h])
  exact (div_le_div_of_nonneg_right hs0 (by positivity)).trans hc

/-- Explicit scalar error in the sector comparison. -/
def error (τ H D : ℝ) (h d folds : ℕ) (E : Expression) : ℝ :=
  let Y := lowerHeight A P τ
  let n := newtonDepth A P τ
  let t := exponent A P+4
  let B := (3/2:ℝ)^n
  let C := QuantitativeArithmeticRetainedFilterTrace.traceMajorant A P n
  (2*Real.sqrt (localizedErrorBound t (4*Real.pi) Y)*Real.sqrt (massSlope t (4*Real.pi) Y))*
    (Real.sqrt (2*h+2:ℝ))⁻¹+
  (expressionBound E+(E.length:ℝ))*uniformRetainedTraceError D Y H h folds+
  ((2*d+2:ℝ)*τ/P.ε)/(4*Real.pi)+
  2*((2+2*C*majorantConstant t (4*Real.pi) P.ε)*Real.sqrt
    (QuantitativeArithmeticRetainedFilterTrace.traceError A P (rawTolerance A P τ) Y n d))+
  upperCutError (B^2*(1+majorantConstant t (4*Real.pi) P.ε)) B 1
    (massBound (2*h) t (4*Real.pi) H/(2*h+2:ℝ))

/-- The fixed certificate supplies this constant; there is no matrix-bound
hypothesis left to prove for the normalized mixed reconstruction. -/
def normalizerMatrixHeight (τ : ℝ) : ℝ :=
  let C := Classical.choose (normalized_matrix_bound A P hS hN)
  2*scaledMatrixHeight A P C (rawTolerance A P τ)*
    (16*scaledMatrixHeight A P C (rawTolerance A P τ)^2)^(4^newtonDepth A P τ)

theorem normalizerMatrixHeight_nonneg (τ : ℝ) : 0≤normalizerMatrixHeight A P hS hN τ := by
  have hc := (Classical.choose_spec (normalized_matrix_bound A P hS hN)).1
  have hb := scaledMatrixHeight_one_le A P hc (rawTolerance A P τ)
  unfold normalizerMatrixHeight
  positivity

/-- For the literal quantified mixed expression, integer matrix geometry is
proved from the original row heights. Only explicit scalar inequalities
remain as inputs to the final asymptotic parameter choice. -/
theorem quantified_sector_le_source (hdiv : ∀p∈S,p∣Q) (hbad : ∀p∈S,p∣N)
    {τ : ℝ} (hτ : 0<τ) (H : ℝ) (hH : 0<H) (h : ℕ) (e : Sector N)
    (qs : Finset ι) (r : ι → Row N) (s : ι → Set ℍ) (hs : ∀i,IsCompact (s i))
    {L U R : ℝ} (hL : 0<L) (hR : 0≤R)
    (hre : ∀i z,z∈s i → |z.re|≤1) (hlo : ∀i z,z∈s i → L≤z.im)
    (hhi : ∀i z,z∈s i → z.im≤U) (hr : ∀i∈qs,quantifiedRowHeight hN (r i) L U≤R)
    (d : ℕ) (Z : Finset ℤ)
    (herr0 : 0<QuantitativeArithmeticRetainedFilterTrace.traceError A P
      (rawTolerance A P τ) (lowerHeight A P τ) (newtonDepth A P τ) d)
    (herr1 : QuantitativeArithmeticRetainedFilterTrace.traceError A P
      (rawTolerance A P τ) (lowerHeight A P τ) (newtonDepth A P τ) d≤1)
    (hsmall : (h+1:ℝ)^(-(1/3:ℝ))*
      ((4*(normalizerMatrixHeight A P hS hN τ)^2*
        (2*max 1 (8*R^2*(normalizerMatrixHeight A P hS hN τ)^2))^d)*(H+2))≤1)
    (hfar : ∀a : ℤ,a∉Z → 2*compactBaseBound (lowerHeight A P τ) H 1≤1+|(a:ℝ)|) :
    let E := quantified A P hS hN τ e qs r s hs hL hre hlo hhi d
    let B := normalizerMatrixHeight A P hS hN τ
    let D := (4*B^2*(2*max 1 (8*R^2*B^2))^d)*(H+2)
    (Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P.s) e):ℝ)/(2*h+2:ℝ)≤
      signedTrace volume (fun z =>
        (QuantitativeArithmeticRetainedFilterExpression.regularSourceFilter A P hS hN e qs r s hs d z).comp
          (AsymptoticOrbitDiagonal.corner (AsymptoticCertificateOperators.highStrip P.ε) z))/(4*Real.pi)+
        error A P τ H D h d Z.card E := by
  dsimp only
  let B := normalizerMatrixHeight A P hS hN τ
  let M := 4*B^2*(2*max 1 (8*R^2*B^2))^d
  let E := quantified A P hS hN τ e qs r s hs hL hre hlo hhi d
  have hB := normalizerMatrixHeight_nonneg A P hS hN τ
  have hM : 0≤M := by dsimp only [M]; positivity
  have hb : ExpressionMatrixBound (normalizedExpression A P hS hN τ e) B :=
    (Classical.choose_spec (normalized_matrix_bound A P hS hN)).2 τ e
  have hm : ExpressionMatrixBound E M :=
    quantified_matrix_bound A P hS hN τ e qs r s hs hL hre hlo hhi hR hB hr hb d
  have hph := quantified_physical A P hS hN τ e qs r s hs hL hre hlo hhi d (h+1)
  have hreg := funext (quantified_regular A P hS hN τ e qs r s hs hL hre hlo hhi d)
  have ht := sector_le_source A P hS hN hdiv hbad hτ H (M*(H+2)) hH
    (mul_nonneg hM (by linarith)) h e qs r s hs d E hph hreg Z herr0 herr1 hsmall hfar
    (hm.geometry hM (lowerHeight A P τ) H Z)
  simpa only [error,add_assoc,E,M,B] using ht

/-- The literal Euler-product solution count, with mixed reconstruction
and all trace comparisons discharged. -/
theorem original_count_le_source (hdiv : ∀p∈S,p∣Q) (hbad : ∀p∈S,p∣N)
    {τ : ℝ} (hτ : 0<τ) (H : ℝ) (hH : 0<H) (h : ℕ)
    (qs : Finset ι) (r : ι → Row N) (s : ι → Set ℍ) (hs : ∀i,IsCompact (s i))
    {L U R : ℝ} (hL : 0<L) (hR : 0≤R)
    (hre : ∀i z,z∈s i → |z.re|≤1) (hlo : ∀i z,z∈s i → L≤z.im)
    (hhi : ∀i z,z∈s i → z.im≤U) (hr : ∀i∈qs,quantifiedRowHeight hN (r i) L U≤R)
    (d : ℕ) (Z : Finset ℤ)
    (herr0 : 0<QuantitativeArithmeticRetainedFilterTrace.traceError A P
      (rawTolerance A P τ) (lowerHeight A P τ) (newtonDepth A P τ) d)
    (herr1 : QuantitativeArithmeticRetainedFilterTrace.traceError A P
      (rawTolerance A P τ) (lowerHeight A P τ) (newtonDepth A P τ) d≤1)
    (hsmall : (h+1:ℝ)^(-(1/3:ℝ))*
      ((4*(normalizerMatrixHeight A P hS hN τ)^2*
        (2*max 1 (8*R^2*(normalizerMatrixHeight A P hS hN τ)^2))^d)*(H+2))≤1)
    (hfar : ∀a : ℤ,a∉Z → 2*compactBaseBound (lowerHeight A P τ) H 1≤1+|(a:ℝ)|) :
    let B := normalizerMatrixHeight A P hS hN τ
    let D := (4*B^2*(2*max 1 (8*R^2*B^2))^d)*(H+2)
    ((FinitenessOriginalInput.S N (2*(h+1))).ncard:ℝ)/(2*h+2:ℝ)≤
      ∑e : Sector N,
        (signedTrace volume (fun z =>
          (QuantitativeArithmeticRetainedFilterExpression.regularSourceFilter A P hS hN e qs r s hs d z).comp
            (AsymptoticOrbitDiagonal.corner (AsymptoticCertificateOperators.highStrip P.ε) z))/(4*Real.pi)+
          error A P τ H D h d Z.card (quantified A P hS hN τ e qs r s hs hL hre hlo hhi d)) := by
  dsimp only
  have hc := (original_count A P hS hN hdiv hbad h).2
  have hc' : ((FinitenessOriginalInput.S N (2*(h+1))).ncard:ℝ)≤
      ∑e : Sector N,(Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P.s) e):ℝ) := by
    exact_mod_cast hc
  apply (div_le_div_of_nonneg_right hc' (by positivity : 0≤(2*h+2:ℝ))).trans
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro e _
  exact quantified_sector_le_source A P hS hN hdiv hbad hτ H hH h e qs r s hs hL hR hre hlo hhi hr
    d Z herr0 herr1 hsmall hfar

#print axioms original_count_le_source
#print axioms normalizerMatrixHeight_nonneg
#print axioms quantified_sector_le_source
#print axioms sector_le_source
#print axioms finiteAmbient_norm
#print axioms finiteAmbient_terminal
#print axioms finiteAmbient_trace_finite
#print axioms fixed_source_error
#print axioms retained_lift
#print axioms geometric_comparison
#print axioms retained_source_bound
#print axioms regularFilter_norm
#print axioms regularFilter_measurable
#print axioms regularFilter_positive
#print axioms regularFilter_trace_finite
#print axioms retained_le_source
#print axioms finite_retained_error
#print axioms cylinderFilter_norm
end QuantitativeArithmeticRetainedGeometricTrace
