module

public import QuantitativeArithmeticRetainedCommonCostV1
public import QuantitativeEulerEndpointActualRowEnvelopeV1
public import QuantitativeEulerEndpointActualGramExponentialV1
public import QuantitativeEulerEndpointScheduledExpressionCostV1

/-! The actual mixed-certificate finite filter: scheduled effort, original
row expressions, regular approximation, and quantitative expression costs.
The certificate-independent row envelopes and polynomial estimates are reused. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticRetainedIteration
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeEulerEndpointPrepared QuantitativeArithmeticRetainedTerminalAlgebra
open QuantitativeEulerEndpointNestedExpression QuantitativeEulerEndpointExponentialParameters
open scoped Classical MatrixGroups

variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime)
  (hN : 2≤N) (excluded : Finset ℕ) (threshold₀ : ℕ) (sector : Sector N)
  (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
  (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)
local notation "area" => P.ε⁻¹

/-- A uniform logarithmic degree/depth budget for the actual explicitly
normalized blocks. The hypotheses on z are exactly the degree fields
retained by the constructed regular iteration. -/
theorem exists_actual_logarithmic_cost (hBg0 : 0≤Bg) (hD0 : 0≤D) (hH₀ : 0≤H₀)
    (hG0 : 0≤G) (hC0 : 0≤C) (hK0 : 0≤Kobs) :
    ∃ K : ℝ,0≤K ∧ ∀ n : ℕ,
      let b := actualBlock A P hR₀ hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs n
      ∀ z : ℕ → ℝ[X],
      (∀ j,j<n → (z j).natDegree≤16*(sharpnessAt A P hR₀ sector n b (j+1))^5+1) →
      (∑ j∈Finset.range n,logarithmicCost (fun i => power (effortAt A P hR₀ sector n b i)) z j)≤K*(4:ℝ)^n ∧
      (budget (fun i => power (effortAt A P hR₀ sector n b i)) z n:ℝ)≤Real.exp (K*(4:ℝ)^n) := by
  obtain ⟨K,hK,hbound⟩ := exists_actual_total_effort A P hR₀ hN excluded threshold₀ sector S hS W
    B Bg D H₀ G C Kobs hBg0 hD0 hH₀ hG0 hC0 hK0
  have ha : 0≤area := inv_nonneg.mpr P.epsilon_pos.le
  refine ⟨scheduleConstant area+17*K,add_nonneg (scheduleConstant_nonneg ha) (by positivity),?_⟩
  intro n b z hz
  have hE (j : ℕ) (_hj : j≤n) : 0≤effortAt A P hR₀ sector n b j :=
    (actualBlock_effort_pos A P hR₀ hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs hK0 n j).le
  have hsum := scheduled_cost_geometric n (effortAt A P hR₀ sector n b) z ha hE hz (hbound n)
  exact ⟨hsum,budget_le_exp _ z n hsum⟩

#print axioms exists_actual_logarithmic_cost

/-- Every scheduled sharpening has a common exponential envelope in the
horizon, derived from the already proved total effort. -/
theorem exists_actual_sharpness_bound (hBg0 : 0≤Bg) (hD0 : 0≤D) (hH₀ : 0≤H₀)
    (hG0 : 0≤G) (hC0 : 0≤C) (hK0 : 0≤Kobs) :
    ∃ K : ℝ,0≤K ∧ ∀ n j : ℕ,j≤n →
      (sharpnessAt A P hR₀ sector n
        (actualBlock A P hR₀ hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs n) j:ℝ)+1≤
          Real.exp (K*(4:ℝ)^n) := by
  obtain ⟨K,hK,hbound⟩ := exists_actual_total_effort A P hR₀ hN excluded threshold₀ sector S hS W
    B Bg D H₀ G C Kobs hBg0 hD0 hH₀ hG0 hC0 hK0
  have ha : 0≤area := inv_nonneg.mpr P.epsilon_pos.le
  refine ⟨280*area+3+3*K,by positivity,?_⟩
  intro n j hj
  let b := actualBlock A P hR₀ hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs n
  let E := effortAt A P hR₀ sector n b
  have hE (i : ℕ) : 0≤E i :=
    (actualBlock_effort_pos A P hR₀ hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs hK0 n i).le
  have hs : 0≤∑ i∈Finset.range n,E i := Finset.sum_nonneg (fun i _ => hE i)
  have he : E j≤K*(4:ℝ)^n := by
    have ht := hbound n
    change (∑ i∈Finset.range n,E i)+E n≤K*(4:ℝ)^n at ht
    rcases eq_or_lt_of_le hj with rfl | hj
    · linarith
    · have hi := Finset.single_le_sum (fun i (_hi : i∈Finset.range n) => hE i) (Finset.mem_range.mpr hj)
      linarith [hE n]
  have hh := sharpness_exp_upper ha (hE j)
  have he' := Real.exp_le_exp.mpr (show 3*E j≤(3*K)*(4:ℝ)^n by nlinarith)
  have hc : 0≤280*area+3 := by positivity
  exact hh.trans ((mul_le_mul_of_nonneg_left he' hc).trans
    (QuantitativeEulerEndpointPolynomialGrowth.scaled_exp_le hc (one_le_pow₀ (by norm_num))))

/-- All outgoing sharpening coefficient masses have a common double
exponential bound; the hypothesis is the actual retained mass field. -/
theorem exists_actual_coefficient_bound (hBg0 : 0≤Bg) (hD0 : 0≤D) (hH₀ : 0≤H₀)
    (hG0 : 0≤G) (hC0 : 0≤C) (hK0 : 0≤Kobs) :
    ∃ K : ℝ,0≤K ∧ ∀ n : ℕ,
      let b := actualBlock A P hR₀ hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs n
      ∀ z : ℕ → ℝ[X],
      (∀ j,j<n → (∑ i∈(z j).support,|(z j).coeff i|)≤
        (((16*(sharpnessAt A P hR₀ sector n b (j+1))^5:ℕ):ℝ)+2)*3^(16*(sharpnessAt A P hR₀ sector n b (j+1))^5)) →
      ∀ j,j<n → (∑ i∈(z j).support,|(z j).coeff i|)≤Real.exp (Real.exp (K*(4:ℝ)^n)) := by
  obtain ⟨K,hK,hbound⟩ := exists_actual_sharpness_bound A P hR₀ hN excluded threshold₀ sector S hS W
    B Bg D H₀ G C Kobs hBg0 hD0 hH₀ hG0 hC0 hK0
  refine ⟨QuantitativeEulerEndpointPolynomialGrowth.initialBaseConstant K,?_,?_⟩
  · unfold QuantitativeEulerEndpointPolynomialGrowth.initialBaseConstant
    positivity
  intro n b z hz j hj
  exact (hz j hj).trans (QuantitativeEulerEndpointPolynomialGrowth.sharpening_coefficient_double_exp
    hK (one_le_pow₀ (by norm_num)) (hbound n (j+1) hj))

#print axioms exists_actual_sharpness_bound
#print axioms exists_actual_coefficient_bound
end QuantitativeArithmeticRetainedIteration

namespace QuantitativeArithmeticRetainedIteration
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeEulerEndpointPrepared QuantitativeArithmeticRetainedTerminalAlgebra
open QuantitativeEulerEndpointNestedExpression QuantitativeEulerEndpointExponentialParameters
open scoped Classical MatrixGroups

/-- Uniform double-exponential residual amplification for any sequence
having the degree and mass fields of the actual bounded iteration. -/
theorem exists_actual_residual_bound {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q}
    (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime)
    (hN : 2≤N) (excluded : Finset ℕ) (threshold₀ : ℕ) (sector : Sector N)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)
    (hBg0 : 0≤Bg) (hD0 : 0≤D) (hH₀ : 0≤H₀) (hG0 : 0≤G) (hC0 : 0≤C) (hK0 : 0≤Kobs) :
    ∃ K : ℝ,0≤K ∧ ∀ n : ℕ,
      let b := actualBlock A P hR₀ hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs n
      ∀ z : ℕ → ℝ[X],
      (∀ j,j<n → (z j).natDegree≤16*(sharpnessAt A P hR₀ sector n b (j+1))^5+1) →
      (∀ j,j<n → (∑ i∈(z j).support,|(z j).coeff i|)≤
        (((16*(sharpnessAt A P hR₀ sector n b (j+1))^5:ℕ):ℝ)+2)*3^(16*(sharpnessAt A P hR₀ sector n b (j+1))^5)) →
      QuantitativeEulerEndpointResidual.errorBudget
        (fun i => power (effortAt A P hR₀ sector n b i)) z n≤Real.exp (Real.exp (K*(4:ℝ)^n)) := by
  obtain ⟨Kl,hKl,hlog⟩ := exists_actual_logarithmic_cost A P hR₀ hN excluded threshold₀ sector S hS W
    B Bg D H₀ G C Kobs hBg0 hD0 hH₀ hG0 hC0 hK0
  obtain ⟨Kc,hKc,hcoef⟩ := exists_actual_coefficient_bound A P hR₀ hN excluded threshold₀ sector S hS W
    B Bg D H₀ G C Kobs hBg0 hD0 hH₀ hG0 hC0 hK0
  refine ⟨Kl+Kc+16,by positivity,?_⟩
  intro n b z hd hm
  let R : ℝ := (4:ℝ)^n
  let V : ℝ := Real.exp (Real.exp ((Kc+16)*R))
  have hR : 1≤R := one_le_pow₀ (by norm_num)
  have hV : 16≤V := by
    have hc : 16≤(Kc+16)*R := by nlinarith
    dsimp only [V]
    linarith [Real.add_one_le_exp ((Kc+16)*R),Real.add_one_le_exp (Real.exp ((Kc+16)*R))]
  have hc : Kc*R≤(Kc+16)*R := by nlinarith
  have hm' (j : ℕ) (hj : j<n) : (∑ i∈(z j).support,|(z j).coeff i|)≤V :=
    (hcoef n z hm j hj).trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hc))
  have hvlog : Real.log V≤Real.exp ((Kc+16)*R) := by
    dsimp only [V]
    rw [Real.log_exp]
  have hh := QuantitativeEulerEndpointResidual.errorBudget_double_exp
    (fun i => power (effortAt A P hR₀ sector n b i)) z hV n hm' (hlog n z hd).1 hvlog
  convert hh using 1
  dsimp only [R]
  congr 2
  ring

#print axioms exists_actual_residual_bound
end QuantitativeArithmeticRetainedIteration

namespace QuantitativeArithmeticRetainedIteration
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointExponentialParameters
open QuantitativeEulerEndpointNestedPerturbation QuantitativeEulerEndpointResidual
open scoped Classical MatrixGroups

/-- Actual degree and mass estimates bound the operator-comparison budget,
in addition to the previously checked fixed-solution residual budget. -/
theorem exists_actual_comparison_bound {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q}
    (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime)
    (hN : 2≤N) (excluded : Finset ℕ) (threshold₀ : ℕ) (sector : Sector N)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)
    (hBg0 : 0≤Bg) (hD0 : 0≤D) (hH₀ : 0≤H₀) (hG0 : 0≤G) (hC0 : 0≤C) (hK0 : 0≤Kobs) :
    ∃ K : ℝ,0≤K ∧ ∀ n : ℕ,
      let b := actualBlock A P hR₀ hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs n
      ∀ z : ℕ → ℝ[X],
      (∀ j,j<n → (z j).natDegree≤16*(sharpnessAt A P hR₀ sector n b (j+1))^5+1) →
      (∀ j,j<n → (∑ i∈(z j).support,|(z j).coeff i|)≤
        (((16*(sharpnessAt A P hR₀ sector n b (j+1))^5:ℕ):ℝ)+2)*3^(16*(sharpnessAt A P hR₀ sector n b (j+1))^5)) →
      comparisonBudget (fun i => power (effortAt A P hR₀ sector n b i)) z n≤Real.exp (Real.exp (K*(4:ℝ)^n)) := by
  obtain ⟨K,hK,hbound⟩ := exists_actual_residual_bound A P hR₀ hN excluded threshold₀ sector S hS W
    B Bg D H₀ G C Kobs hBg0 hD0 hH₀ hG0 hC0 hK0
  refine ⟨K+2,by positivity,?_⟩
  intro n b z hd hm
  have he := hbound n z hd hm
  exact (comparisonBudget_le_square _ z n).trans (squared_double_exp
    (one_le_pow₀ (by norm_num)) (by linarith [errorBudget_ge_one (fun i => power (effortAt A P hR₀ sector n b i)) z n]) he)

#print axioms exists_actual_comparison_bound
end QuantitativeArithmeticRetainedIteration

namespace QuantitativeArithmeticRetainedIteration
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns
open QuantitativeEulerEndpointPrepared QuantitativeHolomorphic AsymptoticFiniteBranch
open QuantitativeEulerEndpointBlockNormalization
open scoped Classical MatrixGroups
variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime) (e : Sector N)

/-- Finite rows with their original quantitative bounds and BOTH exact
representations, selected before the reconstruction expression. -/
structure ReplacementRows (b : Block A P hR₀ e) (r : ℝ × ℝ) where
  baseline : NewBaselineIndex N → Expression
  prime : Fin b.primes.length → Expression
  baseline_bound : ∀ i,expressionBound (baseline i)≤
    wideBaselineRowBound N e (r.1+1) r.2 r.1 ((QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P)+4) i ∧
    ExpressionMatrixBound (baseline i) (baselineMatrixHeight N (r.1+1) r.2 r.1 i)
  prime_bound : ∀ i,expressionBound (prime i)≤
    wideSequenceBound N (sign e.1) (r.1+1) r.2 r.1 ((QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P)+4) b.primes i ∧
    ExpressionMatrixBound (prime i)
      (4*(1+(wideCompactCutoff (N*b.primes[i.val].val^3:ℕ) (r.1+1) r.2 r.1:ℝ))*(N*b.primes[i.val].val^3:ℕ))
  regular : ∀ u x,regularSum (combinedGramExpression baseline prime
      ((factor b.bound (b.primes.length+1):ℝ):ℂ) u) x=
    QuantitativeArithmeticRetainedPacket.replacementGram A P e b.compact b.primes b.bound x (regularSum u x)
  physical : ∀ u m,holomorphicSum (combinedGramExpression baseline prime
      ((factor b.bound (b.primes.length+1):ℝ):ℂ) u) m=
    holomorphicSum (combinedGramExpression
      (originalBaselineExpression N e b.compact P.epsilon_pos
        ((QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P)+4))
      (originalPacketSequenceExpression b.compact P.epsilon_pos
        N (NeZero.pos N) (sign e.1) ((QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P)+4) b.primes)
      ((factor b.bound (b.primes.length+1):ℝ):ℂ) u) m

def ReplacementRows.expression {b : Block A P hR₀ e} {r : ℝ × ℝ}
    (rows : ReplacementRows A P hR₀ e b r) (u : Expression) : Expression :=
  combinedGramExpression rows.baseline rows.prime ((factor b.bound (b.primes.length+1):ℝ):ℂ) u

variable (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

theorem exists_actual_replacement_rows (n j : ℕ) :
    let b := actualBlock A P hR₀ hN excluded threshold e S hS W B Bg D H₀ G C Kobs n j
    let r := actualRowRectangle N hN excluded threshold Bg D H₀ G C
      P.ε n j
    Nonempty (ReplacementRows A P hR₀ e b r) := by
  intro b r
  have hY : 0<r.2 := div_pos (div_pos
    (lt_min P.epsilon_pos (by norm_num : (0:ℝ)<1/4))
    (wideDistortion_pos _ _ _)) (wideDistortion_pos _ _ _)
  have hre : ∀ z∈b.region,|z.re|≤r.1+1 := fun _ hz => hz.1
  have hlo : ∀ z∈b.region,r.2≤z.im := fun _ hz => hz.2.1
  have hhi : ∀ z∈b.region,z.im≤r.1 := fun _ hz => hz.2.2
  obtain ⟨E,F,hE,hF,h⟩ := QuantitativeArithmeticRetainedPacket.exists_replacement_gram_rows A P e b.compact b.primes hY hre hlo hhi b.bound
  exact ⟨⟨E,F,hE,hF,(fun u => (h u).1),(fun u => (h u).2)⟩⟩

def actualReplacementRows (n j : ℕ) :=
  Classical.choice (exists_actual_replacement_rows A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n j)

/-- A simultaneous family of finite Grams, with original coefficients.
Only its common reconstruction depends on the chosen accuracy. -/
def actualGramExpressions (n : ℕ) (u : Expression) (j : ℕ) : Expression :=
  ReplacementRows.expression A P hR₀ e
    (actualReplacementRows A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n j) u

theorem actualGramExpressions_regular (n : ℕ) (u : Expression) (j : ℕ) (x : UpperHalfPlane) :
    let b := actualBlock A P hR₀ hN excluded threshold e S hS W B Bg D H₀ G C Kobs n j
    regularSum (actualGramExpressions A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n u j) x=
      QuantitativeArithmeticRetainedPacket.replacementGram A P e b.compact b.primes b.bound x (regularSum u x) :=
  (actualReplacementRows A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n j).regular u x

#print axioms exists_actual_replacement_rows
#print axioms actualGramExpressions_regular
end QuantitativeArithmeticRetainedIteration

namespace QuantitativeArithmeticRetainedIteration
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns
open QuantitativeEulerEndpointPrepared QuantitativeHolomorphic AsymptoticFiniteBranch
open QuantitativeEulerEndpointBlockNormalization QuantitativeEulerEndpointPrimeBlocks
open scoped Classical MatrixGroups
variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime)
    (e : Sector N) (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

/-- Actual finite Gram complexity, with a polynomial cost for the actual
rows and a quadratic cost for the common reconstruction. -/
theorem exists_actual_gram_costs (hBg0 : 0≤Bg) (hD0 : 0≤D) (hH₀ : 0≤H₀)
    (hG0 : 0≤G) (hC0 : 0≤C) :
    ∃ M : ℝ,4≤M ∧ ∀ n j : ℕ,j≤n → ∀ u : Expression,∀ R : ℝ,0≤R →
      expressionBound u≤R → ExpressionMatrixBound u R →
      let t := (QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P)+4
      let V := envelope N hN excluded threshold M n n
      let g := actualGramExpressions A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n u j
      expressionBound g≤(2*(72*9^t)^2)*V^(684+720*t)*R^2 ∧
      ExpressionMatrixBound g ((8*36^2)*V^720*R^2) := by
  obtain ⟨M,hM,henv⟩ := exists_actual_row_envelope N hN excluded threshold Bg D H₀ G C
    P.ε e hBg0 hD0 hH₀ hG0 hC0
    P.epsilon_pos
  refine ⟨M,hM,?_⟩
  intro n j hj u R hR hu huM t V g
  let b := actualBlock A P hR₀ hN excluded threshold e S hS W B Bg D H₀ G C Kobs n j
  let rows := actualReplacementRows A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n j
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
end QuantitativeArithmeticRetainedIteration

namespace QuantitativeArithmeticRetainedIteration
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns
open QuantitativeEulerEndpointPrepared QuantitativeHolomorphic AsymptoticFiniteBranch
open QuantitativeEulerEndpointPrimeBlocks
open scoped Classical MatrixGroups
variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime)
    (e : Sector N) (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

theorem exists_actual_gram_exponential (hBg0 : 0≤Bg) (hD0 : 0≤D) (hH₀ : 0≤H₀)
    (hG0 : 0≤G) (hC0 : 0≤C) :
    ∃ K : ℝ,0≤K ∧ ∀ n j : ℕ,j≤n → ∀ u : Expression,∀ R : ℝ,0≤R →
      expressionBound u≤R → ExpressionMatrixBound u R →
      let g := actualGramExpressions A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n u j
      expressionBound g≤Real.exp (K*(4:ℝ)^n)*R^2 ∧
      ExpressionMatrixBound g (Real.exp (K*(4:ℝ)^n)*R^2) := by
  obtain ⟨M,hM,hcost⟩ := exists_actual_gram_costs A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs
    hBg0 hD0 hH₀ hG0 hC0
  have hM1 : 1≤M := by linarith
  let t := (QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P)+4
  let a : ℝ := 2*(72*9^t)^2
  let K₁ := Real.log a+2*((684+720*t:ℕ):ℝ)*envelopeConstant N hN excluded threshold M
  let K₂ := Real.log (8*36^2)+2*(720:ℝ)*envelopeConstant N hN excluded threshold M
  have ha : 1≤a := by
    have hp : (1:ℝ)≤9^t := one_le_pow₀ (by norm_num)
    dsimp only [a]
    nlinarith
  have hc := envelopeConstant_nonneg N hN excluded threshold hM1
  have hk₁ : 0≤K₁ := add_nonneg (Real.log_nonneg ha) (by positivity)
  have hk₂ : 0≤K₂ := add_nonneg (Real.log_nonneg (by norm_num)) (by positivity)
  refine ⟨K₁+K₂,add_nonneg hk₁ hk₂,?_⟩
  intro n j hj u R hR hu huM g
  have hs (c : ℝ) (hca : 1≤c) (r : ℕ) :
      c*(envelope N hN excluded threshold M n n)^r≤
        Real.exp ((Real.log c+2*(r:ℝ)*envelopeConstant N hN excluded threshold M)*(4:ℝ)^n) := by
    have hl := log_max_polynomial_envelope N hN excluded threshold hM1 hca r n
      (le_refl (c*(envelope N hN excluded threshold M n n)^r))
    have he := Real.exp_le_exp.mpr hl
    rw [Real.exp_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))] at he
    exact (le_max_right _ _).trans he
  have h₁ := (hs a ha (684+720*t)).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (show K₁≤K₁+K₂ by linarith) (by positivity)))
  have h₂ := (hs (8*36^2) (by norm_num) 720).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (show K₂≤K₁+K₂ by linarith) (by positivity)))
  have hh := hcost n j hj u R hR hu huM
  exact ⟨hh.1.trans (mul_le_mul_of_nonneg_right h₁ (sq_nonneg R)),
    hh.2.mono (mul_le_mul_of_nonneg_right h₂ (sq_nonneg R))⟩

#print axioms exists_actual_gram_exponential
end QuantitativeArithmeticRetainedIteration

namespace QuantitativeArithmeticRetainedIteration
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns
open QuantitativeHolomorphic AsymptoticFiniteBranch
open scoped Classical MatrixGroups
variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime)
    (e : Sector N) (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

theorem exists_actual_common_gram_cost (hBg0 : 0≤Bg) (hD0 : 0≤D) (hH₀ : 0≤H₀)
    (hG0 : 0≤G) (hC0 : 0≤C) {K : ℝ} (hK : 0≤K) :
    ∃ C' : ℝ,0≤C' ∧ ∀ n j : ℕ,j≤n →
      let E := QuantitativeArithmeticRetainedCommonExpression.expression A P hR₀ (NeZero.pos N)
        (Real.exp ((K+1)*(4:ℝ)^n)) e
      let g := actualGramExpressions A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n E j
      expressionBound g≤Real.exp (Real.exp (C'*(4:ℝ)^n)) ∧
      ExpressionMatrixBound g (Real.exp (Real.exp (C'*(4:ℝ)^n))) := by
  obtain ⟨a,ha,hrows⟩ := exists_actual_gram_exponential A P hR₀ e hN excluded threshold S hS W
    B Bg D H₀ G C Kobs hBg0 hD0 hH₀ hG0 hC0
  obtain ⟨c,hc,hrecon⟩ := QuantitativeArithmeticRetainedCommonExpression.exists_horizon_cost A P hR₀ (NeZero.pos N) hK
  refine ⟨a+c+3,by positivity,?_⟩
  intro n j hj E g
  have hu := hrecon n e
  have hg := hrows n j hj E (Real.exp (Real.exp (c*(4:ℝ)^n))) (Real.exp_pos _).le hu.1 hu.2
  have hs := QuantitativeEulerEndpointBoundedIteration.exp_times_double_exp_square ha hc (one_le_pow₀ (by norm_num : (1:ℝ)≤4) (n:=n))
  exact ⟨hg.1.trans hs,hg.2.mono hs⟩

#print axioms exists_actual_common_gram_cost
end QuantitativeArithmeticRetainedIteration

namespace QuantitativeArithmeticRetainedIteration
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeEulerEndpointPrepared QuantitativeHolomorphic AsymptoticFiniteBranch
open QuantitativeArithmeticRetainedTerminalAlgebra QuantitativeEulerEndpointBernstein
open QuantitativeEulerEndpointExponentialParameters QuantitativeEulerEndpointNestedPerturbation
open scoped Classical MatrixGroups
variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime)
    (e : Sector N) (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

def actualFiniteExpression (n : ℕ) (s : ℝ) (q : ℕ → ℝ[X]) : Expression :=
  let b := actualBlock A P hR₀ hN excluded threshold e S hS W B Bg D H₀ G C Kobs n
  let E := QuantitativeArithmeticRetainedCommonExpression.expression A P hR₀ (NeZero.pos N) s e
  QuantitativeArithmeticRetainedExpressionIteration.iterate A P
    (actualGramExpressions A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n E)
    (fun j => power (effortAt A P hR₀ e n b j)) q n

theorem actualFiniteExpression_error (n : ℕ) (s : ℝ) (F : ℕ → Algebra A P) (q : ℕ → ℝ[X])
    (hinit : F 0=1) (hF : ∀ j<n,0≤F j ∧ F j≤1)
    (hrec : ∀ j<n,F (j+1)=nextAt A P hR₀ e n
      (actualBlock A P hR₀ hN excluded threshold e S hS W B Bg D H₀ G C Kobs n) j (F j) (q j))
    (hq : ∀ j<n,ScalarSharpening (q j)) (x : UpperHalfPlane) :
    ‖rep A P (F n) x-regularSum
      (actualFiniteExpression A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n s q) x‖≤
      comparisonBudget (fun j => power (effortAt A P hR₀ e n
        (actualBlock A P hR₀ hN excluded threshold e S hS W B Bg D H₀ G C Kobs n) j)) q n*Real.exp (-8*s) := by
  apply common_expression_comparison A P hR₀ e n _ s F q _ hinit hF hrec hq
  · intro j _ i x
    exact actualBlock_uncomposed_norm A P hR₀ hN excluded threshold e S hS W B Bg D H₀ G C Kobs n j i x
  · intro j _ x
    exact actualGramExpressions_regular A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n _ j x

/-- The literal finite expression for the actual bounded blocks has error
at most 2/4^n. The accuracy constant is fixed before the horizon and before
the sharpening polynomials or regular root are selected. -/
theorem exists_actual_finite_approximation (hBg0 : 0≤Bg) (hD0 : 0≤D) (hH₀ : 0≤H₀)
    (hG0 : 0≤G) (hC0 : 0≤C) (hK0 : 0≤Kobs) :
    ∃ K : ℝ,0≤K ∧ ∀ n : ℕ,
      let b := actualBlock A P hR₀ hN excluded threshold e S hS W B Bg D H₀ G C Kobs n
      ∀ F : ℕ → Algebra A P,∀ q : ℕ → ℝ[X],
      F 0=1 → (∀ j<n,0≤F j ∧ F j≤1) →
      (∀ j<n,F (j+1)=nextAt A P hR₀ e n b j (F j) (q j)) →
      (∀ j<n,ScalarSharpening (q j)) →
      (∀ j<n,(q j).natDegree≤16*(sharpnessAt A P hR₀ e n b (j+1))^5+1) →
      (∀ j<n,(∑ i∈(q j).support,|(q j).coeff i|)≤
        (((16*(sharpnessAt A P hR₀ e n b (j+1))^5:ℕ):ℝ)+2)*3^(16*(sharpnessAt A P hR₀ e n b (j+1))^5)) →
      ∀ x,‖rep A P (F n) x-regularSum (actualFiniteExpression A P hR₀ e hN excluded threshold
        S hS W B Bg D H₀ G C Kobs n (Real.exp ((K+1)*(4:ℝ)^n)) q) x‖≤2/(4:ℝ)^n := by
  obtain ⟨K,hK,hbudget⟩ := exists_actual_comparison_bound A P hR₀ hN excluded threshold e S hS W
    B Bg D H₀ G C Kobs hBg0 hD0 hH₀ hG0 hC0 hK0
  refine ⟨K,hK,?_⟩
  intro n b F q hi hF hr hq hd hm x
  have he := actualFiniteExpression_error A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs
    n (Real.exp ((K+1)*(4:ℝ)^n)) F q hi hF hr hq x
  have hp := QuantitativeEulerEndpointCommonReconstruction.amplified_error_le hK
    (one_le_pow₀ (by norm_num : (1:ℝ)≤4) (n:=n)) (hbudget n q hd hm)
  apply he.trans
  rw [show (2:ℝ)/(4:ℝ)^n=2*(1/(4:ℝ)^n) by ring]
  nlinarith only [hp]

#print axioms actualFiniteExpression_error
#print axioms exists_actual_finite_approximation
end QuantitativeArithmeticRetainedIteration

namespace QuantitativeArithmeticRetainedIteration
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeHolomorphic AsymptoticFiniteBranch
open QuantitativeEulerEndpointExponentialParameters
open scoped Classical MatrixGroups
variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime)
    (e : Sector N) (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

/-- The ACTUAL full-terminal finite filter, with chosen original block
rows and common reconstruction, has uniform double-exponential coefficient
and integer-matrix complexity. No Gram-growth assumption is introduced. -/
theorem exists_actual_terminal_expression_cost (hBg0 : 0≤Bg) (hD0 : 0≤D) (hH₀ : 0≤H₀)
    (hG0 : 0≤G) (hC0 : 0≤C) (hK0 : 0≤Kobs) {K : ℝ} (hK : 0≤K) :
    ∃ C' : ℝ,0≤C' ∧ ∀ n : ℕ,
      let b := actualBlock A P hR₀ hN excluded threshold e S hS W B Bg D H₀ G C Kobs n
      ∀ q : ℕ → ℝ[X],
      (∀ j<n,(q j).natDegree≤16*(sharpnessAt A P hR₀ e n b (j+1))^5+1) →
      (∀ j<n,(∑ i∈(q j).support,|(q j).coeff i|)≤
        (((16*(sharpnessAt A P hR₀ e n b (j+1))^5:ℕ):ℝ)+2)*3^(16*(sharpnessAt A P hR₀ e n b (j+1))^5)) →
      let T := actualFiniteExpression A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs
        n (Real.exp ((K+1)*(4:ℝ)^n)) q
      expressionBound T≤Real.exp (Real.exp (C'*(4:ℝ)^n)) ∧
      ExpressionMatrixBound T (Real.exp (Real.exp (C'*(4:ℝ)^n))) := by
  obtain ⟨Kg,hKg,hgram⟩ := exists_actual_common_gram_cost A P hR₀ e hN excluded threshold S hS W
    B Bg D H₀ G C Kobs hBg0 hD0 hH₀ hG0 hC0 hK
  obtain ⟨Kq,hKq,hcoef⟩ := exists_actual_coefficient_bound A P hR₀ hN excluded threshold e S hS W
    B Bg D H₀ G C Kobs hBg0 hD0 hH₀ hG0 hC0 hK0
  obtain ⟨Kl,hKl,hlog⟩ := exists_actual_logarithmic_cost A P hR₀ hN excluded threshold e S hS W
    B Bg D H₀ G C Kobs hBg0 hD0 hH₀ hG0 hC0 hK0
  let Cb := 16+Kg+Kq
  have hCb : 16≤Cb := by dsimp only [Cb]; linarith
  refine ⟨Kl+Cb,by linarith,?_⟩
  intro n b q hd hm T
  let E := QuantitativeArithmeticRetainedCommonExpression.expression A P hR₀ (NeZero.pos N)
    (Real.exp ((K+1)*(4:ℝ)^n)) e
  let g := actualGramExpressions A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n E
  let R : ℝ := (4:ℝ)^n
  let B' := Real.exp (Real.exp (Cb*R))
  have hR : 1≤R := one_le_pow₀ (by norm_num)
  have hB' : 16≤B' := by
    have hcr : 16≤Cb*R := by nlinarith
    dsimp only [B']
    linarith [Real.add_one_le_exp (Cb*R),Real.add_one_le_exp (Real.exp (Cb*R))]
  have hg' (j : ℕ) (hj : j<n) : expressionBound (g j)≤B' ∧ ExpressionMatrixBound (g j) B' := by
    have hh := hgram n j hj.le
    have hb : Real.exp (Real.exp (Kg*R))≤B' :=
      Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by dsimp only [Cb]; nlinarith))
    exact ⟨hh.1.trans hb,hh.2.mono hb⟩
  have hq' (j : ℕ) (hj : j<n) : (∑ i∈(q j).support,|(q j).coeff i|)≤B' :=
    (hcoef n q hm j hj).trans
      (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by dsimp only [Cb]; nlinarith)))
  have hb : Real.log B'≤Real.exp (Cb*R) := by
    dsimp only [B']
    rw [Real.log_exp]
  have ht := QuantitativeArithmeticRetainedExpressionIteration.bounds A P g
    (fun j => power (effortAt A P hR₀ e n b j)) q hB' n (fun j hj => (hg' j hj).1)
    (fun j hj => (hg' j hj).2) hq' (hlog n q hd).1 hb
  have he : Kl*R+Cb*R=(Kl+Cb)*R := by ring
  rw [he] at ht
  exact ht

#print axioms exists_actual_terminal_expression_cost
end QuantitativeArithmeticRetainedIteration

namespace QuantitativeArithmeticRetainedIteration
open AsymptoticSectorSigns QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight QuantitativeHolomorphic
open QuantitativeEulerEndpointPrepared QuantitativeArithmeticRetainedTerminalAlgebra Polynomial AsymptoticFiniteBranch
open scoped Classical MatrixGroups

/-- Actual full-terminal regular filters and their literal finite branch
approximants, with paid error and complexity, retaining the trace estimate
and common-kernel preservation of the original normalized iteration. -/
theorem exists_actual_finite_filter {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q}
    (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime) (hN2 : 2≤N)
    (sector : Sector N) (threshold : ℕ) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N) :
    let excluded := reconstructionExclusions N Q ∪ R₀
    let G := generatorTransportConstant (QuantitativeEulerEndpointPrepared.prepared N hN2 excluded threshold)
    ∃ (W : Finset (List SL(2,ℤ))) (Bobs : ℝ),1≤Bobs ∧
      ∃ Bg : ℝ,1≤Bg ∧ ∃ D : ℝ,1≤D ∧ ∃ C : ℝ,1≤C ∧ ∃ Kobs : ℝ,0≤Kobs ∧
      ∀ H₀ : ℝ,max P.ε⁻¹ 4≤H₀ →
      (∀ i,sectorFamilyB N (NeZero.pos N) sector S hS i≤H₀) →
      ∃ Ka Kc : ℝ,0≤Ka ∧ 0≤Kc ∧ ∀ n : ℕ,
      let H := H₀*(4:ℝ)^n
      let b := actualBlock A P hR₀ hN2 excluded threshold sector S hS W Bobs Bg D H₀ G C Kobs n
      let target := sectorTraceTarget N (NeZero.pos N) sector S hS H P.epsilon_pos (by omega : 1≤(QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P)+4)+H⁻¹
      ∃ (F : ℕ → Algebra A P) (z : ℕ → ℝ[X]),F 0=1 ∧
        (∀ j,j≤n → Valid A P hR₀ sector n b j (F j)) ∧
        (∀ j,j<n → Step A P hR₀ sector n b target j (F j) (z j) ∧
          F (j+1)=nextAt A P hR₀ sector n b j (F j) (z j)) ∧
        (∀ E : Algebra A P,
          (∀ j,j<n → ∀ i : Fin ((b j).primes.length+1),∀ x,
            QuantitativeArithmeticRetainedPacket.rows A P hR₀ sector (b j).compact (b j).primes i x*rep A P E x=0) →
          ∀ j,j≤n → F j*E=E) ∧
        tr A P (F n)≤target+Real.exp ((8:ℝ)/3+8)*
          (P.ε⁻¹+4*(1+P.ε⁻¹*Real.log 2))/(4:ℝ)^n ∧
        let T := actualFiniteExpression A P hR₀ sector hN2 excluded threshold S hS W Bobs Bg D H₀ G C Kobs
          n (Real.exp ((Ka+1)*(4:ℝ)^n)) z
        expressionBound T≤Real.exp (Real.exp (Kc*(4:ℝ)^n)) ∧
        ExpressionMatrixBound T (Real.exp (Real.exp (Kc*(4:ℝ)^n))) ∧
        ∀ x,‖rep A P (F n) x-regularSum T x‖≤2/(4:ℝ)^n := by
  intro excluded G
  obtain ⟨W,Bobs,hBobs,Bg,hBg,D,hD,C,hC,Kobs,hKobs,hiteration⟩ :=
    exists_bounded_prime_block_iteration A P hR₀ hN2 sector threshold S hS
  refine ⟨W,Bobs,hBobs,Bg,hBg,D,hD,C,hC,Kobs,hKobs,?_⟩
  intro H₀ hH₀ hdata
  have hH₀0 : 0≤H₀ := by have h4 := (le_max_right P.ε⁻¹ 4).trans hH₀; linarith
  have hG : 0≤G := (generatorTransportConstant_pos _).le
  obtain ⟨Ka,hKa,happrox⟩ := exists_actual_finite_approximation A P hR₀ sector hN2 excluded threshold S hS W
    Bobs Bg D H₀ G C Kobs (by linarith) (by linarith) hH₀0 hG (by linarith) hKobs
  obtain ⟨Kc,hKc,hcost⟩ := exists_actual_terminal_expression_cost A P hR₀ sector hN2 excluded threshold S hS W
    Bobs Bg D H₀ G C Kobs (by linarith) (by linarith) hH₀0 hG (by linarith) hKobs hKa
  refine ⟨Ka,Kc,hKa,hKc,?_⟩
  intro n H b target
  have hHH : H₀≤H := by
    have hp : (1:ℝ)≤4^n := one_le_pow₀ (by norm_num)
    dsimp only [H]
    nlinarith
  obtain ⟨F,z,hi,hvalid,hrec,hfix,htrace⟩ :=
    hiteration n (fun _ => C) (fun _ _ => le_rfl) H
      (hH₀.trans hHH) (fun i => (hdata i).trans hHH)
  have hd (j : ℕ) (hj : j<n) : (z j).natDegree≤16*(sharpnessAt A P hR₀ sector n b (j+1))^5+1 :=
    (hrec j hj).1.degree
  have hm (j : ℕ) (hj : j<n) : (∑ i∈(z j).support,|(z j).coeff i|)≤
      (((16*(sharpnessAt A P hR₀ sector n b (j+1))^5:ℕ):ℝ)+2)*3^(16*(sharpnessAt A P hR₀ sector n b (j+1))^5) :=
    (hrec j hj).1.mass
  have hc := hcost n z hd hm
  refine ⟨F,z,hi,hvalid,hrec,hfix,htrace,hc.1,hc.2,?_⟩
  exact happrox n F z hi (fun j hj => ⟨(hvalid j hj.le).nonneg,(hvalid j hj.le).le_one⟩)
    (fun j hj => (hrec j hj).2) (fun j hj => (hrec j hj).1.scalar) hd hm

#print axioms exists_actual_finite_filter
end QuantitativeArithmeticRetainedIteration
