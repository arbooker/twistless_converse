module

public import QuantitativeArithmeticRetainedExpressionIterationV1
public import QuantitativeEulerEndpointReplacementGramExpressionV1
public import QuantitativeEulerEndpointReplacementGramSupportV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedCommonExpression
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns
open QuantitativeArithmeticRetainedFiniteTransport QuantitativeArithmeticRetainedFiniteNormalization
open QuantitativeArithmeticRetainedFilterExpression QuantitativeHolomorphic AsymptoticFiniteBranch
open ContinuousLinearMap

private theorem transport_norm
    {E F H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (I : E →L[ℂ] H) (hI : I.adjoint.comp I=1)
    (J : F →L[ℂ] H) (hJ : J.adjoint.comp J=1)
    (V : E →L[ℂ] F) (hV : ‖V‖≤1) : ‖J.comp (V.comp I.adjoint)‖≤1 := by
  have hh := norm_isometric_transport_difference_le I hI J hJ V (0 : E →L[ℂ] F)
  simp only [zero_comp,comp_zero,sub_zero] at hh
  exact hh.trans hV

private theorem source_identity
    {E F H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : E →L[ℂ] F) (I : E →L[ℂ] H) (T : H →L[ℂ] H)
    (hI : I.adjoint.comp I=1) (hT : I.comp I.adjoint=T) :
    (V.comp I.adjoint).comp T=V.comp I.adjoint := by
  have hr : I.adjoint.comp (I.comp I.adjoint)=I.adjoint := by
    rw [←comp_assoc,hI]
    exact id_comp _
  rw [←hT,comp_assoc,hr]

variable {N Q : ℕ} {R₀ : Finset ℕ} {hQ : 0<Q}
  (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime) (hN : 0<N)

def expression (s : ℝ) (e : Sector N) : Expression :=
  normalizedExpression A P hR₀ hN (Real.exp (-8*s)/2) e

theorem regular_error (s : ℝ) (e : Sector N) (x : UpperHalfPlane) :
    ‖regularSum (expression A P hR₀ hN s e) x-regularAmbient A P hR₀ hN e x‖≤Real.exp (-8*s)/2 :=
  regular_ambient_error A P hR₀ hN (half_pos (Real.exp_pos _)) e x

theorem regular_norm (s : ℝ) (e : Sector N) (x : UpperHalfPlane) :
    ‖regularSum (expression A P hR₀ hN s e) x‖≤1 := by
  unfold expression
  rw [regular_normalized]
  have hh := transport_norm
    (QuantitativeArithmeticRetainedRegularExtension.TerminalSpace A P x).subtypeL
    (AsymptoticOrbitRegion.adjoint_comp_subtype _ x)
    (1 : RegularSpace →L[ℂ] RegularSpace) ((norm_map_iff_adjoint_comp_self (1 : RegularSpace →L[ℂ] RegularSpace)).1 (fun _ => rfl))
    _ (polynomialNormalizedReconstruction_norm_le _ (regularScaled_norm A P hR₀ hN (rawTolerance A P (Real.exp (-8*s)/2))
      (lowerHeight A P (Real.exp (-8*s)/2)) e x) (newtonDepth A P (Real.exp (-8*s)/2)))
  simpa only [one_def,id_comp] using hh

theorem physical_norm (s : ℝ) (e : Sector N) (m : ℕ) :
    ‖holomorphicSum (expression A P hR₀ hN s e) m‖≤1 := by
  unfold expression
  rw [physical_normalized]
  exact transport_norm (AsymptoticCylinderTerminal.ambientLift P.ε)
    (AsymptoticCylinderTerminal.ambientLift_adjoint_self _) AsymptoticCylinderLift.lift.toContinuousLinearMap
    AsymptoticCylinderLift.lift.adjoint_comp_self _
    (polynomialNormalizedReconstruction_norm_le _ (physicalScaled_norm A P hR₀ hN _ _ e m) _)

theorem regular_right_terminal (s : ℝ) (e : Sector N) (x : UpperHalfPlane) :
    regularSum (expression A P hR₀ hN s e) x*
      regularSum (QuantitativeArithmeticRetainedExpressionIteration.unit A P) x=
      regularSum (expression A P hR₀ hN s e) x := by
  rw [QuantitativeArithmeticRetainedExpressionIteration.unit_regular,
    QuantitativeArithmeticRetainedTerminalAlgebra.rep_one]
  unfold expression
  rw [regular_normalized]
  apply source_identity
  · exact AsymptoticOrbitRegion.adjoint_comp_subtype _ x
  · rw [Submodule.adjoint_subtypeL]
    rfl

#print axioms regular_error
#print axioms regular_norm
#print axioms physical_norm
#print axioms regular_right_terminal
end QuantitativeArithmeticRetainedCommonExpression

namespace QuantitativeArithmeticRetainedPacket
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns QuantitativeHolomorphic
open AsymptoticRegularCompactBranch ContinuousLinearMap
open QuantitativeEulerEndpointBlockNormalization QuantitativeEulerEndpointPrepared
open QuantitativeArithmeticRetainedPreparedReconstruction

variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (P : Parameters A) (e : Sector N)
variable {s : Set UpperHalfPlane} (hs : IsCompact s) (l : List (EligiblePrime N))

/-- The baseline square root cancels for any replacement reconstruction,
with the exact original block normalization retained on every row. -/
theorem replacementGram_expansion (C : ℕ → ℝ) (x : UpperHalfPlane) (U : Space →L[ℂ] Space) :
    let r : ℂ := (factor C (l.length+1):ℝ)
    replacementGram A P e hs l C x U=
      (∑ i : NewBaselineIndex N,star (r • (newBaselineRows N e hs P.epsilon_pos (exponent A P+4) x i*U))*
        (r • (newBaselineRows N e hs P.epsilon_pos (exponent A P+4) x i*U)))+
      ∑ i : Fin l.length,star (r • (packetSequence N (NeZero.pos N) (sign e.1) hs P.epsilon_pos (exponent A P+4) l i x*U))*
        (r • (packetSequence N (NeZero.pos N) (sign e.1) hs P.epsilon_pos (exponent A P+4) l i x*U)) := by
  intro r
  unfold replacementGram finiteRowGram
  rw [Fin.sum_univ_succ]
  simp only [smul_comp]
  change star (r • (newBaselineDetector N e hs P.epsilon_pos (exponent A P+4) x*U))*
    (r • (newBaselineDetector N e hs P.epsilon_pos (exponent A P+4) x*U))+_= _
  have hh := absolute_stack_composed_gram (newBaselineRows N e hs P.epsilon_pos (exponent A P+4) x) (r • U)
  apply congrArg₂ (fun X Y : Space →L[ℂ] Space => X+Y)
  · simpa only [newBaselineDetector,mul_smul_comm] using hh
  · rfl

#print axioms replacementGram_expansion
end QuantitativeArithmeticRetainedPacket

namespace QuantitativeArithmeticRetainedPacket
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns
open QuantitativeHolomorphic AsymptoticFiniteBranch
open QuantitativeEulerEndpointBlockNormalization QuantitativeEulerEndpointPrepared
open QuantitativeArithmeticRetainedPreparedReconstruction
open scoped Classical
variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (P : Parameters A)
    (e : Sector N) {s : Set UpperHalfPlane} (hs : IsCompact s) (l : List (EligiblePrime N))

theorem replacementGram_support (C : ℕ → ℝ) (x : UpperHalfPlane)
    (U T : RegularSpace →L[ℂ] RegularSpace) (hT : IsStarProjection T) (hU : U*T=U) :
    T*replacementGram A P e hs l C x U=replacementGram A P e hs l C x U ∧
      replacementGram A P e hs l C x U*T=replacementGram A P e hs l C x U := by
  have hh := scaled_gram_sum_support T hT
    (fun i : Fin (l.length+1) => uncomposedCombinedRows A P e hs l i x)
    ((factor C (l.length+1):ℝ):ℂ) U hU
  have he : replacementGram A P e hs l C x U=
      ∑ i : Fin (l.length+1),
        star (((factor C (l.length+1):ℝ):ℂ) • (uncomposedCombinedRows A P e hs l i x*U))*
          (((factor C (l.length+1):ℝ):ℂ) • (uncomposedCombinedRows A P e hs l i x*U)) := by
    unfold replacementGram finiteRowGram
    apply Finset.sum_congr rfl
    intro i _
    change star ((((factor C (l.length+1):ℝ):ℂ) • uncomposedCombinedRows A P e hs l i x)*U)*
      ((((factor C (l.length+1):ℝ):ℂ) • uncomposedCombinedRows A P e hs l i x)*U)=_
    rw [smul_mul_assoc]
  rw [he]
  exact hh

#print axioms replacementGram_support
end QuantitativeArithmeticRetainedPacket

namespace QuantitativeArithmeticRetainedPacket
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns QuantitativeHolomorphic
open AsymptoticRegularCompactBranch AsymptoticFiniteBranch
open QuantitativeEulerEndpointBlockNormalization QuantitativeEulerEndpointPrepared
open QuantitativeArithmeticRetainedPreparedReconstruction
open scoped Classical

variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (P : Parameters A) (e : Sector N)
variable {s : Set UpperHalfPlane} (hs : IsCompact s) (l : List (EligiblePrime N))

/-- One explicitly bounded set of row expressions realizes the actual
replacement Gram and its original physical rows with the same coefficients.
The reconstruction expression is arbitrary and chosen afterwards. -/
theorem exists_replacement_gram_rows {R Y H : ℝ} (hY : 0<Y)
    (hre : ∀ z∈s,|z.re|≤R) (hlo : ∀ z∈s,Y≤z.im) (hhi : ∀ z∈s,z.im≤H) (C : ℕ → ℝ) :
    let r : ℂ := (factor C (l.length+1):ℝ)
    ∃ (E : NewBaselineIndex N → Expression) (F : Fin l.length → Expression),
      (∀ i,expressionBound (E i)≤wideBaselineRowBound N e R Y H (exponent A P+4) i ∧
        ExpressionMatrixBound (E i) (baselineMatrixHeight N R Y H i)) ∧
      (∀ i,expressionBound (F i)≤wideSequenceBound N (sign e.1) R Y H (exponent A P+4) l i ∧
        ExpressionMatrixBound (F i)
          (4*(1+(wideCompactCutoff (N*l[i.val].val^3:ℕ) R Y H:ℝ))*(N*l[i.val].val^3:ℕ))) ∧
      ∀ u : Expression,
      (∀ x,regularSum (combinedGramExpression E F r u) x=replacementGram A P e hs l C x (regularSum u x)) ∧
      (∀ m,holomorphicSum (combinedGramExpression E F r u) m=
        holomorphicSum (combinedGramExpression
          (originalBaselineExpression N e hs P.epsilon_pos (exponent A P+4))
          (originalPacketSequenceExpression hs P.epsilon_pos N (NeZero.pos N) (sign e.1) (exponent A P+4) l) r u) m) := by
  intro r
  obtain ⟨E,hE⟩ := exists_baseline_expressions hs P.epsilon_pos hY hre hlo hhi N e (exponent A P+4)
  obtain ⟨F,hF⟩ := exists_sequence_expression_physical hs P.epsilon_pos hY hre hlo hhi
    N (NeZero.pos N) (sign e.1) (exponent A P+4) l
  refine ⟨E,(fun i => F i),(fun i => (hE i).2.2),(fun i => (hF i).2.2),?_⟩
  intro u
  constructor
  · intro x
    rw [regular_combinedGramExpression,replacementGram_expansion]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      rw [(hE i).1 x]
    · apply Finset.sum_congr rfl
      intro i _
      rw [(hF i).1 x]
  · intro m
    rw [holomorphic_combinedGramExpression,holomorphic_combinedGramExpression]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      rw [(hE i).2.1 m]
    · apply Finset.sum_congr rfl
      intro i _
      rw [(hF i).2.1 m]

#print axioms exists_replacement_gram_rows
end QuantitativeArithmeticRetainedPacket
