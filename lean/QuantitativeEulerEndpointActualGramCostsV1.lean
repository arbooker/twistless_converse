module

public import QuantitativeEulerEndpointActualReplacementRowsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBoundedIteration
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeEulerEndpointPrepared QuantitativeHolomorphic AsymptoticFiniteBranch
open QuantitativeEulerEndpointBlockNormalization QuantitativeEulerEndpointPrimeBlocks
open scoped Classical MatrixGroups
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
    (e : Sector N) (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

/-- Actual finite Gram complexity, with a polynomial cost for the actual
rows and a quadratic cost for the common reconstruction. -/
theorem exists_actual_gram_costs (hBg0 : 0≤Bg) (hD0 : 0≤D) (hH₀ : 0≤H₀)
    (hG0 : 0≤G) (hC0 : 0≤C) :
    ∃ M : ℝ,4≤M ∧ ∀ n j : ℕ,j≤n → ∀ u : Expression,∀ R : ℝ,0≤R →
      expressionBound u≤R → ExpressionMatrixBound u R →
      let t := (AsymptoticReconstructedCount.parameters A P).s+4
      let V := envelope N hN excluded threshold M n n
      let g := actualGramExpressions A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n u j
      expressionBound g≤(2*(72*9^t)^2)*V^(684+720*t)*R^2 ∧
      ExpressionMatrixBound g ((8*36^2)*V^720*R^2) := by
  obtain ⟨M,hM,henv⟩ := exists_actual_row_envelope N hN excluded threshold Bg D H₀ G C
    (AsymptoticReconstructedCount.parameters A P).ε e hBg0 hD0 hH₀ hG0 hC0
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos
  refine ⟨M,hM,?_⟩
  intro n j hj u R hR hu huM t V g
  let b := actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n j
  let rows := actualReplacementRows A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n j
  let U := V^36
  have hv : 1≤V := (show (1:ℝ)≤M by linarith).trans
    (envelope_base N hN excluded threshold (by linarith) n n)
  have hu1 : 1≤U := one_le_pow₀ hv
  have hh := henv n j hj
  have hbase (i : NewBaselineIndex N) : expressionBound (rows.baseline i)≤72*9^t*U^(9+10*t) :=
    (rows.baseline_bound i).1.trans ((hh.2.2.2 t).1 i).1
  have hprime (i : Fin b.primes.length) : expressionBound (rows.prime i)≤72*9^t*U^(9+10*t) :=
    (rows.prime_bound i).1.trans ((hh.2.2.2 t).2 i).1
  have hbaseM (i : NewBaselineIndex N) : ExpressionMatrixBound (rows.baseline i) (36*U^10) :=
    ((rows.baseline_bound i).2).mono ((hh.2.2.2 t).1 i).2
  have hprimeM (i : Fin b.primes.length) : ExpressionMatrixBound (rows.prime i) (36*U^10) :=
    ((rows.prime_bound i).2).mono ((hh.2.2.2 t).2 i).2
  have hfactor : ‖((factor b.bound (b.primes.length+1):ℝ):ℂ)‖≤1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (factor_pos _ _)]
    exact QuantitativeEulerEndpointNormalizedThreshold.factor_le_one _ _
  have hm := combined_mass_le rows.baseline rows.prime _ u hfactor hbase hprime (by positivity) hu
  have hcard : (Fintype.card (NewBaselineIndex N):ℝ)+(Fintype.card (Fin b.primes.length):ℝ)≤2*U := by
    rw [Fintype.card_fin]
    exact hh.2.2.1
  constructor
  · calc
      expressionBound g ≤ ((Fintype.card (NewBaselineIndex N):ℝ)+(Fintype.card (Fin b.primes.length):ℝ))*
          (72*9^t*U^(9+10*t)*R)^2 := hm
      _ ≤ (2*U)*(72*9^t*U^(9+10*t)*R)^2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
      _ = _ := by
        dsimp only [U]
        rw [mul_pow,mul_pow,←pow_mul,←pow_mul]
        ring
  · have hmM := combined_matrix rows.baseline rows.prime
      (((factor b.bound (b.primes.length+1):ℝ)):ℂ) u (by positivity : (0:ℝ)≤36*U^10)
      hR hbaseM hprimeM huM
    have he : 8*(36*U^10)^2*R^2=(8*36^2)*V^720*R^2 := by
      dsimp only [U]
      ring
    rw [he] at hmM
    exact hmM

#print axioms exists_actual_gram_costs
end QuantitativeEulerEndpointBoundedIteration
