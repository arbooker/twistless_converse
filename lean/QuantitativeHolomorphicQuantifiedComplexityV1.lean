module

public import QuantitativeHolomorphicQuantifiedFilterV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open AsymptoticFiniteBranch AsymptoticCompactObservationCount AsymptoticSectorSigns
open FinitenessCertificate FinitenessGlobalHeight

theorem observationFilterExpression_complexity_le {ι : Type*} (qs : Finset ι)
    (rows : ι → Expression) (v : Expression) (b a : ι → ℝ) (l : ι → ℕ)
    {V : ℝ} {K : ℕ} (hV : expressionBound v ≤ V) (hK : v.length ≤ K)
    (ha : ∀ i∈qs, expressionBound (rows i) ≤ a i)
    (hl : ∀ i∈qs, (rows i).length ≤ l i) (d : ℕ) :
    expressionBound (observationFilterExpression qs rows v b d) ≤
      V^2*(1+∑ i∈qs, (a i*V)^2)^d ∧
    (observationFilterExpression qs rows v b d).length ≤
      K^2*(1+∑ i∈qs, (l i*K)^2)^d := by
  have hV0 := (expressionBound_nonneg v).trans hV
  have hsum : (∑ i∈qs, (expressionBound (rows i)*expressionBound v)^2) ≤
      ∑ i∈qs, (a i*V)^2 := by
    apply Finset.sum_le_sum
    intro i hi
    apply pow_le_pow_left₀ (mul_nonneg (expressionBound_nonneg _) (expressionBound_nonneg _))
    exact mul_le_mul (ha i hi) hV (expressionBound_nonneg _) ((expressionBound_nonneg _).trans (ha i hi))
  have hsum0 : 0 ≤ ∑ i∈qs, (expressionBound (rows i)*expressionBound v)^2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hbase : 1≤finiteRowBound qs b := by
    unfold finiteRowBound
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have hinv : (finiteRowBound qs b)⁻¹≤1 := inv_le_one_of_one_le₀ hbase
  have hs := (mul_le_of_le_one_left hsum0 hinv).trans hsum
  have he := observationFilterExpression_complexity qs rows v b d
  constructor
  · rw [he.1]
    apply mul_le_mul (pow_le_pow_left₀ (expressionBound_nonneg _) hV 2)
      (pow_le_pow_left₀ (by positivity) (add_le_add le_rfl hs) d) (by positivity) (sq_nonneg V)
  · rw [he.2]
    apply Nat.mul_le_mul (Nat.pow_le_pow_left hK 2)
    apply Nat.pow_le_pow_left
    apply Nat.add_le_add_left
    apply Finset.sum_le_sum
    intro i hi
    exact Nat.pow_le_pow_left (Nat.mul_le_mul (hl i hi) hK) 2

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) {ι : Type*}

def certificateMatrixBase (hN : 0<N) : ℝ :=
  Classical.choose (scaledCutCountExpression_uniform_matrix_height A hN)

def rawCountMatrixHeight (hN : 0<N) (j J : ℕ) : ℝ :=
  let B := 2*(1+(J:ℝ))*certificateMatrixBase A hN
  8*max 1 (2*(2*B)^j*B)

theorem rawCountMatrixHeight_one_le (hN : 0<N) (j J : ℕ) :
    1≤rawCountMatrixHeight A hN j J := by
  unfold rawCountMatrixHeight
  have hh := le_max_left (1:ℝ) (2*(2*(2*(1+(J:ℝ))*certificateMatrixBase A hN))^j*
    (2*(1+(J:ℝ))*certificateMatrixBase A hN))
  linarith

theorem scaledCutCountExpression_explicit_height (hN : 0<N) (P : Parameters A)
    (e : Sector N) (Y : ℝ) (j J : ℕ) :
    ExpressionMatrixBound (scaledCutCountExpression A hN P e Y j J)
      (rawCountMatrixHeight A hN j J) :=
  (Classical.choose_spec (scaledCutCountExpression_uniform_matrix_height A hN)).2 P e Y j J

def normalizedCountMatrixHeight (hN : 0<N) (j J n : ℕ) : ℝ :=
  2*rawCountMatrixHeight A hN j J*(16*(rawCountMatrixHeight A hN j J)^2)^(4^n)

def quantifiedFilterMatrixHeight (hN : 0<N) (qs : Finset ι) (r : ι → Row N)
    (L U : ℝ) (j J n d : ℕ) : ℝ :=
  let R := ∑ i∈qs, quantifiedRowHeight hN (r i) L U
  let V := normalizedCountMatrixHeight A hN j J n
  4*V^2*(2*max 1 (8*R^2*V^2))^d

theorem quantifiedFilterMatrixHeight_nonneg (hN : 0<N) (qs : Finset ι) (r : ι → Row N)
    (L U : ℝ) (j J n d : ℕ) : 0≤quantifiedFilterMatrixHeight A hN qs r L U j J n d := by
  unfold quantifiedFilterMatrixHeight
  positivity

theorem quantifiedCountFilterExpression_matrix_bound (hN : 0<N) (P : Parameters A) (e : Sector N)
    (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane) (hs : ∀ i, IsCompact (s i))
    {L U : ℝ} (hL : 0<L)
    (hre : ∀ i z, z∈s i → |z.re|≤1) (hlo : ∀ i z, z∈s i → L≤z.im)
    (hhi : ∀ i z, z∈s i → z.im≤U) (Y : ℝ) (j J n d : ℕ) :
    ExpressionMatrixBound (quantifiedCountFilterExpression A hN P e qs r s hs hL hre hlo hhi Y j J n d)
      (quantifiedFilterMatrixHeight A hN qs r L U j J n d) := by
  apply expressionMatrixBound_observationFilter
  · exact Finset.sum_nonneg (fun i _ => quantifiedRowHeight_nonneg hN (r i) L U)
  · unfold normalizedCountMatrixHeight
    have hb := rawCountMatrixHeight_one_le A hN j J
    positivity
  · intro i hi
    apply (quantifiedRowExpression_spec hN (r i) e (hs i) hL _ (hre i) (hlo i) (hhi i) _).2.2.2.2.mono
    exact Finset.single_le_sum (fun i _ => quantifiedRowHeight_nonneg hN (r i) L U) hi
  · exact expressionMatrixBound_normalized (rawCountMatrixHeight_one_le A hN j J)
      (scaledCutCountExpression_explicit_height A hN P e Y j J) n

/-- Both combinatorial costs of the complete filter are controlled by
the explicit row cutoffs and the existing finite Newton reconstruction.
The qualitative observation norm bounds no longer enter this estimate. -/
theorem quantifiedCountFilterExpression_complexity (hN : 0<N) (P : Parameters A) (e : Sector N)
    (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane) (hs : ∀ i, IsCompact (s i))
    {L U : ℝ} (hL : 0<L)
    (hre : ∀ i z, z∈s i → |z.re|≤1) (hlo : ∀ i z, z∈s i → L≤z.im)
    (hhi : ∀ i z, z∈s i → z.im≤U) (Y : ℝ) (j J n d : ℕ) :
    let E := quantifiedCountFilterExpression A hN P e qs r s hs hL hre hlo hhi Y j J n d
    let R := scaledCutCountExpression A hN P e Y j J
    let V := expressionBound R*(3+expressionBound R^2)^(4^n)
    let K := R.length*(3+R.length^2)^(4^n)
    expressionBound E ≤ V^2*(1+∑ i∈qs,
      (quantifiedRowMass hN (r i) L U ((AsymptoticReconstructedCount.parameters A P).s+4)*V)^2)^d ∧
    E.length ≤ K^2*(1+∑ i∈qs, (quantifiedRowLength hN (r i) L U*K)^2)^d := by
  have hn := normalizedReconstructionExpression_complexity (scaledCutCountExpression A hN P e Y j J) n
  apply observationFilterExpression_complexity_le qs _ _ _ _ _ hn.1 hn.2
  · intro i _
    exact (quantifiedRowExpression_spec hN (r i) e (hs i) hL _ (hre i) (hlo i) (hhi i) _).2.2.2.1
  · intro i _
    exact (quantifiedRowExpression_spec hN (r i) e (hs i) hL _ (hre i) (hlo i) (hhi i) _).2.2.1.le

#print axioms observationFilterExpression_complexity_le
#print axioms quantifiedCountFilterExpression_matrix_bound
#print axioms quantifiedCountFilterExpression_complexity

end QuantitativeHolomorphic
