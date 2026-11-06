module

public import QuantitativeEulerEndpointPhysicalNormalizationV1
public import QuantitativeEulerEndpointCommonPhysicalSupportV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBoundedIteration
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeEulerEndpointPrepared QuantitativeHolomorphic AsymptoticFiniteBranch
open QuantitativeEulerEndpointPhysicalNormalization
open scoped Classical MatrixGroups
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
    (e : Sector N) (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

/-- The selected physical Gram is a positive contraction with precisely
the stored regular-block normalization, for every physical weight. -/
theorem actualGramExpressions_physical_order (n j m : ℕ) (u : Expression)
    (hu : ‖holomorphicSum u m‖≤1) :
    let g := actualGramExpressions A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n u j
    0≤holomorphicSum g m ∧ holomorphicSum g m≤1 := by
  intro g
  let b := actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n j
  let rows := actualReplacementRows A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n j
  let r := actualRowRectangle N hN excluded threshold Bg D H₀ G C
    (AsymptoticReconstructedCount.parameters A P).ε n j
  let t := (AsymptoticReconstructedCount.parameters A P).s+4
  let cb := wideBaselineRowBound N e (r.1+1) r.2 r.1 t
  let cp := fun i : Fin b.primes.length => wideSequenceBound N (sign e.1) (r.1+1) r.2 r.1 t b.primes i
  have hb (i : NewBaselineIndex N) : ‖holomorphicSum (rows.baseline i) m‖≤cb i :=
    (holomorphicSum_norm_le _ _).trans (rows.baseline_bound i).1
  have hp (i : Fin b.primes.length) : ‖holomorphicSum (rows.prime i) m‖≤cp i :=
    (holomorphicSum_norm_le _ _).trans (rows.prime_bound i).1
  let : Nontrivial RegularSpace := ⟨⟨AsymptoticRegularTrace.delta 1,0,by
    intro he
    have hh := congrArg (fun v : RegularSpace => v 1) he
    simp [AsymptoticRegularTrace.delta] at hh⟩⟩
  have hbase : (∑ i,(cb i)^2)≤(wideDetectorBound N e (r.1+1) r.2 r.1 t)^2 :=
    baseline_square_le cb (wideBaselineRowBound_nonneg N e _ _ _ t)
      (pi_conversion_norm_ge_one (ι:=NewBaselineIndex N) (J:=RegularSpace))
  have hs : (∑ i,(cb i)^2)+(∑ i,(cp i)^2)≤∑ i : Fin (b.primes.length+1),(b.bound i)^2 := by
    rw [Fin.sum_univ_succ]
    exact add_le_add hbase (le_refl (∑ i,(cp i)^2))
  change 0≤holomorphicSum (combinedGramExpression rows.baseline rows.prime _ u) m ∧
    holomorphicSum (combinedGramExpression rows.baseline rows.prime _ u) m≤1
  rw [holomorphic_combinedGramExpression]
  exact combined_order (fun i => holomorphicSum (rows.baseline i) m)
    (fun i => holomorphicSum (rows.prime i) m) cb cp hb hp b.bound (b.primes.length+1) hs _ hu

theorem actualGramExpressions_physical_support (n j m : ℕ) (u : Expression)
    (hu : holomorphicSum u m*holomorphicSum (QuantitativeEulerEndpointTerminalExpression.unit A P) m=
      holomorphicSum u m) :
    let U := holomorphicSum (QuantitativeEulerEndpointTerminalExpression.unit A P) m
    let G := holomorphicSum (actualGramExpressions A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n u j) m
    U*G=G ∧ G*U=G := by
  let rows := actualReplacementRows A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n j
  exact physical_combined_support rows.baseline rows.prime _ u m _
    (QuantitativeEulerEndpointTerminalExpression.unit_physical_projection A P m) hu

#print axioms actualGramExpressions_physical_order
#print axioms actualGramExpressions_physical_support
end QuantitativeEulerEndpointBoundedIteration
