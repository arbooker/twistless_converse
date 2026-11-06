module

public import QuantitativeEulerEndpointActualRowEnvelopeV1
public import QuantitativeEulerEndpointBoundedExpressionComparisonV1
public import QuantitativeEulerEndpointActualGramReplacementV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBoundedIteration
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeEulerEndpointPrepared QuantitativeHolomorphic AsymptoticFiniteBranch
open QuantitativeEulerEndpointBlockNormalization
open scoped Classical MatrixGroups
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A) (e : Sector N)

/-- Finite rows with their original quantitative bounds and BOTH exact
representations, selected before the reconstruction expression. -/
structure ReplacementRows (b : Block A P e) (r : ℝ × ℝ) where
  baseline : NewBaselineIndex N → Expression
  prime : Fin b.primes.length → Expression
  baseline_bound : ∀ i,expressionBound (baseline i)≤
    wideBaselineRowBound N e (r.1+1) r.2 r.1 ((AsymptoticReconstructedCount.parameters A P).s+4) i ∧
    ExpressionMatrixBound (baseline i) (baselineMatrixHeight N (r.1+1) r.2 r.1 i)
  prime_bound : ∀ i,expressionBound (prime i)≤
    wideSequenceBound N (sign e.1) (r.1+1) r.2 r.1 ((AsymptoticReconstructedCount.parameters A P).s+4) b.primes i ∧
    ExpressionMatrixBound (prime i)
      (4*(1+(wideCompactCutoff (N*b.primes[i.val].val^3:ℕ) (r.1+1) r.2 r.1:ℝ))*(N*b.primes[i.val].val^3:ℕ))
  regular : ∀ u x,regularSum (combinedGramExpression baseline prime
      ((factor b.bound (b.primes.length+1):ℝ):ℂ) u) x=
    replacementGram A P e b.compact b.primes b.bound x (regularSum u x)
  physical : ∀ u m,holomorphicSum (combinedGramExpression baseline prime
      ((factor b.bound (b.primes.length+1):ℝ):ℂ) u) m=
    holomorphicSum (combinedGramExpression
      (originalBaselineExpression N e b.compact (AsymptoticReconstructedCount.parameters A P).epsilon_pos
        ((AsymptoticReconstructedCount.parameters A P).s+4))
      (originalPacketSequenceExpression b.compact (AsymptoticReconstructedCount.parameters A P).epsilon_pos
        N (NeZero.pos N) (sign e.1) ((AsymptoticReconstructedCount.parameters A P).s+4) b.primes)
      ((factor b.bound (b.primes.length+1):ℝ):ℂ) u) m

def ReplacementRows.expression {b : Block A P e} {r : ℝ × ℝ}
    (rows : ReplacementRows A P e b r) (u : Expression) : Expression :=
  combinedGramExpression rows.baseline rows.prime ((factor b.bound (b.primes.length+1):ℝ):ℂ) u

variable (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

theorem exists_actual_replacement_rows (n j : ℕ) :
    let b := actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n j
    let r := actualRowRectangle N hN excluded threshold Bg D H₀ G C
      (AsymptoticReconstructedCount.parameters A P).ε n j
    Nonempty (ReplacementRows A P e b r) := by
  intro b r
  have hY : 0<r.2 := div_pos (div_pos
    (lt_min (AsymptoticReconstructedCount.parameters A P).epsilon_pos (by norm_num : (0:ℝ)<1/4))
    (wideDistortion_pos _ _ _)) (wideDistortion_pos _ _ _)
  have hre : ∀ z∈b.region,|z.re|≤r.1+1 := fun _ hz => hz.1
  have hlo : ∀ z∈b.region,r.2≤z.im := fun _ hz => hz.2.1
  have hhi : ∀ z∈b.region,z.im≤r.1 := fun _ hz => hz.2.2
  obtain ⟨E,F,hE,hF,h⟩ := exists_replacement_gram_rows A P e b.compact b.primes hY hre hlo hhi b.bound
  exact ⟨⟨E,F,hE,hF,(fun u => (h u).1),(fun u => (h u).2)⟩⟩

def actualReplacementRows (n j : ℕ) :=
  Classical.choice (exists_actual_replacement_rows A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n j)

/-- A simultaneous family of finite Grams, with original coefficients.
Only its common reconstruction depends on the chosen accuracy. -/
def actualGramExpressions (n : ℕ) (u : Expression) (j : ℕ) : Expression :=
  ReplacementRows.expression A P e
    (actualReplacementRows A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n j) u

theorem actualGramExpressions_regular (n : ℕ) (u : Expression) (j : ℕ) (x : UpperHalfPlane) :
    let b := actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n j
    regularSum (actualGramExpressions A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n u j) x=
      replacementGram A P e b.compact b.primes b.bound x (regularSum u x) :=
  (actualReplacementRows A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n j).regular u x

#print axioms exists_actual_replacement_rows
#print axioms actualGramExpressions_regular
end QuantitativeEulerEndpointBoundedIteration
