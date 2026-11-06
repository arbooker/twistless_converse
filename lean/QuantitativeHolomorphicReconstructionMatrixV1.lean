module

public import QuantitativeHolomorphicNewtonMatrixV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open AsymptoticFiniteBranch FinitenessCertificate FinitenessGlobalHeight
open AsymptoticCertificateBranches AsymptoticSectorSigns
open AsymptoticRegularCertificate AsymptoticCertificateOperators

/-- A finite geometric sum enlarges the height only by its maximal word
length. The number of summands affects coefficient mass, not this bound. -/
theorem ExpressionMatrixBound.geometric {E : Expression} {B : ℝ}
    (hB : 1 ≤ B) (hE : ExpressionMatrixBound E B) (n : ℕ) :
    ExpressionMatrixBound (geometricExpression E n) ((2*B)^n) := by
  have hbase : 1 ≤ 2*B := by linarith
  induction n with
  | zero => intro b hb; simp [geometricExpression] at hb
  | succ n ih =>
    have hp := hE.power (by linarith) n
    have hh := ih.append hp
    exact hh.mono (by simpa using (pow_le_pow_right₀ hbase (Nat.le_succ n)))

theorem expressionMatrixBound_singleton_one (b : Branch) (hb : b.label=1) :
    ExpressionMatrixBound [b] 1 := by
  intro c hc
  have he : c=b := by simpa only [List.mem_singleton] using hc
  subst c
  refine ⟨1,?_,?_⟩
  · rw [hb]; exact integerAction_one
  · intro i j
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- The fixed certificate's individual folded labels control both its
low and terminal expressions. Scalar amplitudes and region indicators
leave the projective labels unchanged. -/
theorem certificateExpressions_matrix_bound (hN : 0<N) (P : Parameters A)
    (χ : ℕ → ℂ) (I : Finset ℤ) {B : ℝ}
    (hfold : ∀ v : Index A, ∀ n ∈ I, ∃ M : IntegerMatrix2,
      IntegerAction (AsymptoticRationalBranches.fold (levelQ_pos A hN v)
        (inputShiftQ A v) (outputShiftQ A v) n) M ∧ MatrixEntryBound M B) :
    ExpressionMatrixBound (lowExpression A hN P χ (P.s+3) I) B ∧
    ExpressionMatrixBound (terminalExpression A hN P χ (by omega : 2≤P.s+3) I) B := by
  constructor
  · apply expressionMatrixBound_sum
    intro v _
    apply ExpressionMatrixBound.scale
    intro b hb
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hb
    exact hfold v n (Finset.mem_toList.mp hn)
  · apply expressionMatrixBound_sum
    intro v _
    apply ExpressionMatrixBound.scale
    intro b hb
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hb
    exact hfold v n (Finset.mem_toList.mp hn)

/-- Explicit height of the actual finite reconstruction, including its
terminal projection and the two compact-height/weight multipliers. -/
theorem cutFullExpression_matrix_bound (hN : 0<N) (P : Parameters A)
    (χ : ℕ → ℂ) (Y : ℝ) (n : ℕ) (I : Finset ℤ) {B : ℝ} (hB : 1≤B)
    (hL : ExpressionMatrixBound (lowExpression A hN P χ (P.s+3) I) B)
    (hT : ExpressionMatrixBound
      (terminalExpression A hN P χ (by omega : 2≤P.s+3) I) B) :
    ExpressionMatrixBound (cutFullExpression A hN P χ Y n I)
      (8*max 1 (2*(2*B)^n*B)) := by
  have hn := (hL.geometric hB n).compose hT (by linarith)
  have hf := (expressionMatrixBound_identity.append hn).compose
    (expressionMatrixBound_singleton_one
      (corner (highStrip P.ε) (highStrip_measurable P.ε)) rfl) zero_le_one
  have hw := (expressionMatrixBound_singleton_one (weight P.epsilon_pos) rfl).compose
    hf (by positivity : 0 ≤ 2*max 1 (2*(2*B)^n*B)*1)
  have hy := (expressionMatrixBound_singleton_one (heightCorner Y) rfl).compose
    hw (by positivity : 0 ≤ 2*1*(2*max 1 (2*(2*B)^n*B)*1))
  convert hy using 1
  · rfl
  · ring

/-- The actual scaled counting reconstruction inherits the same matrix
height, independently of the weight, sector amplitudes and cutoff height. -/
theorem scaledCutCountExpression_matrix_bound (hN : 0<N) (P : Parameters A)
    (e : Sector N) (Y : ℝ) (n J : ℕ) {B : ℝ} (hB : 1≤B)
    (hfold : ∀ v : Index A, ∀ j ∈ Finset.Icc (-(J:ℤ)) J, ∃ M : IntegerMatrix2,
      IntegerAction (AsymptoticRationalBranches.fold (levelQ_pos A hN v)
        (inputShiftQ A v) (outputShiftQ A v) j) M ∧ MatrixEntryBound M B) :
    ExpressionMatrixBound (scaledCutCountExpression A hN P e Y n J)
      (8*max 1 (2*(2*B)^n*B)) := by
  obtain ⟨hl,ht⟩ := certificateExpressions_matrix_bound A hN
    (AsymptoticReconstructedCount.parameters A P) (multiplier e) _ hfold
  exact (cutFullExpression_matrix_bound A hN
    (AsymptoticReconstructedCount.parameters A P) (multiplier e) Y n _ hB hl ht).scale _

#print axioms certificateExpressions_matrix_bound
#print axioms cutFullExpression_matrix_bound
#print axioms scaledCutCountExpression_matrix_bound

end QuantitativeHolomorphic
