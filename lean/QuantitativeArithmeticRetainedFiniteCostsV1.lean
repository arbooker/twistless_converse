module

public import QuantitativeArithmeticRetainedFiniteTransportV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedFiniteTransport
open ContinuousLinearMap AsymptoticFiniteBranch AsymptoticSectorSigns
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedFiniteNormalization
open QuantitativeArithmeticRetainedCylinderNormalization (bound bound_one_le)
open QuantitativeHolomorphic

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ) (P : Parameters A)
    (hS : ∀p∈S,p.Prime) (hN : 0<N)

/-- Count actual primitive folds and retained affine folds separately. -/
def rowLength (j : Fin Q) (J : ℕ) :
    SpanningIntegerRows.AugIndex N (S:Set ℕ) Q → ℕ
  | Sum.inl i => (AsymptoticCertificateBranches.residues i.val.1).card*(2*J+1)
  | Sum.inr i => (QuantitativeArithmeticRetainedDilationOperator.folds
      (i.1.val:ℝ) ((i.1.val:ℝ)*QuantitativeArithmeticRetainedCertificateOperators.shift j i.2)).card

def certificateLength (J : ℕ) : ℕ :=
  ∑ j : Fin Q,∑ i∈(A.coeff j).support,rowLength (S:=S) j J i

theorem rowLength_linear (j : Fin Q) (J : ℕ)
    (i : SpanningIntegerRows.AugIndex N (S:Set ℕ) Q) :
    rowLength j J i≤(2*J+1)*rowLength j 0 i := by
  cases i with
  | inl i => simp [rowLength,Nat.mul_comm]
  | inr i =>
    exact Nat.le_mul_of_pos_left _ (by omega)

theorem certificateLength_linear (J : ℕ) :
    certificateLength A J≤(2*J+1)*certificateLength A 0 := by
  unfold certificateLength
  simp only [Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun i _ => rowLength_linear j J i))

theorem row_lengths (χ β : ℕ → ℂ) (j : Fin Q) {t : ℕ} (ht : 2≤t) (J : ℕ)
    (i : SpanningIntegerRows.AugIndex N (S:Set ℕ) Q) :
    (QuantitativeArithmeticRetainedFiniteExpressions.rowLowExpression A hS hN P χ β j t
      (Finset.Icc (-(J:ℤ)) J) i).length=rowLength j J i ∧
    (QuantitativeArithmeticRetainedFiniteExpressions.rowTerminalExpression A hS hN P χ β j ht
      (Finset.Icc (-(J:ℤ)) J) i).length=rowLength j J i := by
  have hI : (Finset.Icc (-(J:ℤ)) J).card=2*J+1 := by rw [Int.card_Icc]; omega
  cases i with
  | inl i =>
    simp [QuantitativeArithmeticRetainedFiniteExpressions.rowLowExpression,
      QuantitativeArithmeticRetainedFiniteExpressions.rowTerminalExpression,
      QuantitativeArithmeticRetainedFiniteExpressions.primitiveLowExpression,
      QuantitativeArithmeticRetainedFiniteExpressions.primitiveTerminalExpression,
      length_sumExpressions,scaleExpression,ofFinset,hI,rowLength]
  | inr i =>
    simp [QuantitativeArithmeticRetainedFiniteExpressions.rowLowExpression,
      QuantitativeArithmeticRetainedFiniteExpressions.rowTerminalExpression,
      QuantitativeArithmeticRetainedFiniteExpressions.retainedLowExpression,
      QuantitativeArithmeticRetainedFiniteExpressions.retainedTerminalExpression,
      scaleExpression,ofFinset,rowLength]

theorem certificate_lengths (χ β : ℕ → ℂ) {t : ℕ} (ht : 2≤t) (J : ℕ) :
    (QuantitativeArithmeticRetainedFiniteExpressions.lowExpression A hS hN P χ β t
      (Finset.Icc (-(J:ℤ)) J)).length=certificateLength A J ∧
    (QuantitativeArithmeticRetainedFiniteExpressions.terminalExpression A hS hN P χ β ht
      (Finset.Icc (-(J:ℤ)) J)).length=certificateLength A J := by
  constructor
  · simp only [QuantitativeArithmeticRetainedFiniteExpressions.lowExpression,length_sumExpressions,
      scaleExpression,List.length_map,(row_lengths A P hS hN χ β _ ht J _).1,certificateLength]
  · simp only [QuantitativeArithmeticRetainedFiniteExpressions.terminalExpression,length_sumExpressions,
      scaleExpression,List.length_map,(row_lengths A P hS hN χ β _ ht J _).2,certificateLength]

def rawLength (δ : ℝ) : ℕ :=
  let M := certificateLength A (QuantitativeArithmeticRetainedFiniteSchedule.cutoff A P δ)
  (∑ j∈Finset.range (QuantitativeArithmeticRetainedFiniteSchedule.depth A P δ),M^j)*(1+M)

theorem scaled_length (δ Y : ℝ) (e : Sector N) :
    (scaledExpression A P hS hN δ Y e).length=rawLength A P δ := by
  have hh := certificate_lengths A P hS hN (multiplier e)
    (QuantitativeArithmeticRetainedSectorReconstruction.ramifiedParameter e)
    (by omega : 2≤QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P+3)
    (QuantitativeArithmeticRetainedFiniteSchedule.cutoff A P δ)
  simp only [scaledExpression,scaleExpression,List.length_map,length_composeExpression,
    List.length_cons,List.length_nil,zero_add,one_mul,mul_one,
    QuantitativeArithmeticRetainedFiniteSchedule.expression,
    QuantitativeArithmeticRetainedFiniteExpressions.fullExpression,length_neumannExpression,
    List.length_append,QuantitativeArithmeticRetainedFiniteExpressions.symmetricFolds,hh.1,hh.2,rawLength]

theorem normalized_length (τ : ℝ) (e : Sector N) :
    (normalizedExpression A P hS hN τ e).length≤
      rawLength A P (rawTolerance A P τ)*
        (3+rawLength A P (rawTolerance A P τ)^2)^(4^newtonDepth A P τ) := by
  simpa only [normalizedExpression,scaled_length] using (normalizedReconstructionExpression_complexity
    (scaledExpression A P hS hN (rawTolerance A P τ) (lowerHeight A P τ) e) (newtonDepth A P τ)).2

theorem scaled_mass (δ Y : ℝ) (e : Sector N) :
    expressionBound (scaledExpression A P hS hN δ Y e)≤1 := by
  have hw : expressionBound [weight P.epsilon_pos]=1 := by simp [expressionBound,weight]
  have hy : expressionBound [heightCorner Y]=1 := by simp [expressionBound,heightCorner,corner]
  rw [scaledExpression,expressionBound_scale,expressionBound_compose,expressionBound_compose,
    hw,hy,one_mul,one_mul]
  have hB : 0<bound A P := zero_lt_one.trans_le (bound_one_le A P)
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hB)]
  exact (mul_le_mul_of_nonneg_left
    (QuantitativeArithmeticRetainedFiniteSchedule.expression_mass A P hS hN δ e)
    (inv_nonneg.mpr hB.le)).trans_eq (inv_mul_cancel₀ hB.ne')

theorem normalized_mass (τ : ℝ) (e : Sector N) :
    expressionBound (normalizedExpression A P hS hN τ e)≤(4:ℝ)^(4^newtonDepth A P τ) := by
  let R := scaledExpression A P hS hN (rawTolerance A P τ) (lowerHeight A P τ) e
  have hR : expressionBound R≤1 := scaled_mass A P hS hN _ _ e
  have hR0 := expressionBound_nonneg R
  apply (normalizedReconstructionExpression_complexity R (newtonDepth A P τ)).1.trans
  have hp : (3+expressionBound R^2)^(4^newtonDepth A P τ)≤(4:ℝ)^(4^newtonDepth A P τ) := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [sq_nonneg (expressionBound R-1)]
  exact (mul_le_mul hR hp (by positivity) zero_le_one).trans_eq (one_mul _)

/-- The actual matrix height after the two scalar height multipliers. -/
def scaledMatrixHeight (C δ : ℝ) : ℝ :=
  16*(4*(1+(QuantitativeArithmeticRetainedFiniteSchedule.cutoff A P δ:ℝ))*C)^(
    QuantitativeArithmeticRetainedFiniteSchedule.depth A P δ)*
    (2*(1+(QuantitativeArithmeticRetainedFiniteSchedule.cutoff A P δ:ℝ))*C)

theorem scaledMatrixHeight_one_le {C : ℝ} (hC : 1≤C) (δ : ℝ) :
    1≤scaledMatrixHeight A P C δ := by
  have hJ : (0:ℝ)≤QuantitativeArithmeticRetainedFiniteSchedule.cutoff A P δ := Nat.cast_nonneg _
  have hb : 1≤4*(1+(QuantitativeArithmeticRetainedFiniteSchedule.cutoff A P δ:ℝ))*C := by nlinarith
  have hc : 1≤2*(1+(QuantitativeArithmeticRetainedFiniteSchedule.cutoff A P δ:ℝ))*C := by nlinarith
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ hb)) hc

theorem scaled_matrix_bound : ∃C : ℝ,1≤C ∧ ∀ (δ Y : ℝ) (e : Sector N),
    ExpressionMatrixBound (scaledExpression A P hS hN δ Y e) (scaledMatrixHeight A P C δ) := by
  obtain ⟨C,hC,hR⟩ := QuantitativeArithmeticRetainedFiniteSchedule.matrix_bound A P hS hN
  refine ⟨C,hC,?_⟩
  intro δ Y e
  have hC0 : 0≤C := zero_le_one.trans hC
  have hw := (expressionMatrixBound_singleton_one (weight P.epsilon_pos) rfl).compose
    (hR δ e) (by positivity)
  have hy := (expressionMatrixBound_singleton_one (heightCorner Y) rfl).compose hw (by positivity)
  have hh := hy.scale (((bound A P)⁻¹:ℝ):ℂ)
  convert hh using 1
  · rfl
  · unfold scaledMatrixHeight
    ring

/-- A single certificate constant controls all normalized expressions,
independently of sector and of the physical weight or regular orbit. -/
theorem normalized_matrix_bound : ∃C : ℝ,1≤C ∧ ∀ (τ : ℝ) (e : Sector N),
    ExpressionMatrixBound (normalizedExpression A P hS hN τ e)
      (2*scaledMatrixHeight A P C (rawTolerance A P τ)*
        (16*scaledMatrixHeight A P C (rawTolerance A P τ)^2)^(4^newtonDepth A P τ)) := by
  obtain ⟨C,hC,hR⟩ := scaled_matrix_bound A P hS hN
  exact ⟨C,hC,fun τ e => expressionMatrixBound_normalized
    (scaledMatrixHeight_one_le A P hC _) (hR _ _ e) _⟩

#print axioms certificateLength_linear
#print axioms scaled_length
#print axioms normalized_length
#print axioms scaled_mass
#print axioms normalized_mass
#print axioms normalized_matrix_bound
end QuantitativeArithmeticRetainedFiniteTransport
