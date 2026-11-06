module

public import QuantitativeEulerEndpointReplacementGramExpansionV1
public import QuantitativeEulerEndpointBaselineRowExpressionV1
public import QuantitativeEulerEndpointPhysicalPacketRowsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns QuantitativeHolomorphic
open AsymptoticRegularCompactBranch AsymptoticFiniteBranch
open QuantitativeEulerEndpointBlockNormalization
open scoped Classical

def combinedGramExpression {ι κ : Type*} [Fintype ι] [Fintype κ]
    (E : ι → Expression) (F : κ → Expression) (a : ℂ) (u : Expression) : Expression :=
  gramExpression (fun i => scaleExpression a (composeExpression (E i) u)) ++
    gramExpression (fun i => scaleExpression a (composeExpression (F i) u))

theorem regular_combinedGramExpression {ι κ : Type*} [Fintype ι] [Fintype κ]
    (E : ι → Expression) (F : κ → Expression) (a : ℂ) (u : Expression) (x : UpperHalfPlane) :
    regularSum (combinedGramExpression E F a u) x=
      (∑ i,star (a • (regularSum (E i) x*regularSum u x))*(a • (regularSum (E i) x*regularSum u x)))+
      ∑ i,star (a • (regularSum (F i) x*regularSum u x))*(a • (regularSum (F i) x*regularSum u x)) := by
  simp only [combinedGramExpression,regularSum_append,regularSum_gramExpression,regularSum_scale,regularSum_compose]
  rfl

theorem holomorphic_combinedGramExpression {ι κ : Type*} [Fintype ι] [Fintype κ]
    (E : ι → Expression) (F : κ → Expression) (a : ℂ) (u : Expression) (m : ℕ) :
    holomorphicSum (combinedGramExpression E F a u) m=
      (∑ i,star (a • (holomorphicSum (E i) m*holomorphicSum u m))*(a • (holomorphicSum (E i) m*holomorphicSum u m)))+
      ∑ i,star (a • (holomorphicSum (F i) m*holomorphicSum u m))*(a • (holomorphicSum (F i) m*holomorphicSum u m)) := by
  simp only [combinedGramExpression,holomorphicSum_append,holomorphicSum_gramExpression,holomorphicSum_scale,holomorphicSum_compose]
  rfl

variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A) (e : Sector N)
variable {s : Set UpperHalfPlane} (hs : IsCompact s) (l : List (EligiblePrime N))

/-- One explicitly bounded set of row expressions realizes the actual
replacement Gram and its original physical rows with the same coefficients.
The reconstruction expression is arbitrary and chosen afterwards. -/
theorem exists_replacement_gram_rows {R Y H : ℝ} (hY : 0<Y)
    (hre : ∀ z∈s,|z.re|≤R) (hlo : ∀ z∈s,Y≤z.im) (hhi : ∀ z∈s,z.im≤H) (C : ℕ → ℝ) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let r : ℂ := (factor C (l.length+1):ℝ)
    ∃ (E : NewBaselineIndex N → Expression) (F : Fin l.length → Expression),
      (∀ i,expressionBound (E i)≤wideBaselineRowBound N e R Y H (P'.s+4) i ∧
        ExpressionMatrixBound (E i) (baselineMatrixHeight N R Y H i)) ∧
      (∀ i,expressionBound (F i)≤wideSequenceBound N (sign e.1) R Y H (P'.s+4) l i ∧
        ExpressionMatrixBound (F i)
          (4*(1+(wideCompactCutoff (N*l[i.val].val^3:ℕ) R Y H:ℝ))*(N*l[i.val].val^3:ℕ))) ∧
      ∀ u : Expression,
      (∀ x,regularSum (combinedGramExpression E F r u) x=replacementGram A P e hs l C x (regularSum u x)) ∧
      (∀ m,holomorphicSum (combinedGramExpression E F r u) m=
        holomorphicSum (combinedGramExpression
          (originalBaselineExpression N e hs P'.epsilon_pos (P'.s+4))
          (originalPacketSequenceExpression hs P'.epsilon_pos N (NeZero.pos N) (sign e.1) (P'.s+4) l) r u) m) := by
  intro P' r
  obtain ⟨E,hE⟩ := exists_baseline_expressions hs P'.epsilon_pos hY hre hlo hhi N e (P'.s+4)
  obtain ⟨F,hF⟩ := exists_sequence_expression_physical hs P'.epsilon_pos hY hre hlo hhi
    N (NeZero.pos N) (sign e.1) (P'.s+4) l
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

#print axioms regular_combinedGramExpression
#print axioms holomorphic_combinedGramExpression
#print axioms exists_replacement_gram_rows
end QuantitativeEulerEndpointPrepared
