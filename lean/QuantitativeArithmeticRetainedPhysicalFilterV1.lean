module

public import QuantitativeArithmeticRetainedActualFiniteV1
public import QuantitativeArithmeticRetainedFilterTraceV1
public import QuantitativeEulerEndpointActualPhysicalPreservationV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedCommonExpression
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open AsymptoticSectorSigns AsymptoticFiniteBranch QuantitativeHolomorphic ContinuousLinearMap
open QuantitativeArithmeticRetainedFiniteTransport
variable {N Q : ℕ} {R₀ : Finset ℕ} {hQ : 0<Q}
  (A : Certificate N R₀ Q hQ) (P : Parameters A)
  (hR₀ : ∀p∈R₀,p.Prime) (hN : 0<N)

/-- Exact normalized mixed reconstruction on the ambient physical space. -/
def physicalExact (h : ℕ) (e : Sector N) :=
  AsymptoticCylinderLift.lift.toContinuousLinearMap.comp
    ((QuantitativeArithmeticRetainedFilterTrace.reconstruction A hR₀ hN P h e).comp
      (AsymptoticCylinderTerminal.ambientLift P.ε).adjoint)

theorem physicalExact_norm (h : ℕ) (e : Sector N) :
    ‖physicalExact A P hR₀ hN h e‖≤1 := by
  have hh := norm_isometric_transport_difference_le
    (AsymptoticCylinderTerminal.ambientLift P.ε)
    (AsymptoticCylinderTerminal.ambientLift_adjoint_self _) AsymptoticCylinderLift.lift.toContinuousLinearMap
    AsymptoticCylinderLift.lift.adjoint_comp_self
    (QuantitativeArithmeticRetainedFilterTrace.reconstruction A hR₀ hN P h e)
    (0 : AsymptoticCylinderTerminal.Space P.ε →L[ℂ] AsymptoticCylinder.Space)
  simp only [zero_comp,comp_zero,sub_zero] at hh
  exact hh.trans (QuantitativeArithmeticRetainedFilterTrace.reconstruction_norm A hR₀ hN P h e)

theorem physical_error (s : ℝ) (e : Sector N) (h : ℕ) :
    ‖holomorphicSum (expression A P hR₀ hN s e) (h+1)-physicalExact A P hR₀ hN h e‖≤
      Real.exp (-8*s)/2 :=
  physical_ambient_error A P hR₀ hN (half_pos (Real.exp_pos _)) e (h+1)

theorem physical_right_terminal (s : ℝ) (e : Sector N) (h : ℕ) :
    holomorphicSum (expression A P hR₀ hN s e) (h+1)*
      holomorphicSum (QuantitativeArithmeticRetainedExpressionIteration.unit A P) (h+1)=
        holomorphicSum (expression A P hR₀ hN s e) (h+1) := by
  rw [QuantitativeArithmeticRetainedExpressionIteration.unit_physical]
  change holomorphicSum (expression A P hR₀ hN s e) (h+1)*
    AsymptoticCylinderTerminal.hyperProjection P.ε=_
  rw [←AsymptoticCylinderTerminal.ambientLift_self_adjoint]
  unfold expression
  rw [physical_normalized]
  exact QuantitativeEulerEndpointCommonReconstruction.transport_right_projection _ _ _
    (AsymptoticCylinderTerminal.ambientLift_adjoint_self _)

#print axioms physicalExact_norm
#print axioms physical_error
#print axioms physical_right_terminal
end QuantitativeArithmeticRetainedCommonExpression

namespace QuantitativeArithmeticRetainedIteration
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns
open QuantitativeEulerEndpointPrepared QuantitativeHolomorphic AsymptoticFiniteBranch
open QuantitativeEulerEndpointPhysicalNormalization
open scoped Classical MatrixGroups
variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime)
    (e : Sector N) (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

/-- The selected physical Gram is a positive contraction with precisely
the stored regular-block normalization, for every physical weight. -/
theorem actualGramExpressions_physical_order (n j m : ℕ) (u : Expression)
    (hu : ‖holomorphicSum u m‖≤1) :
    let g := actualGramExpressions A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n u j
    0≤holomorphicSum g m ∧ holomorphicSum g m≤1 := by
  intro g
  let b := actualBlock A P hR₀ hN excluded threshold e S hS W B Bg D H₀ G C Kobs n j
  let rows := actualReplacementRows A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n j
  let r := actualRowRectangle N hN excluded threshold Bg D H₀ G C
    P.ε n j
  let t := (QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P)+4
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
    (hu : holomorphicSum u m*holomorphicSum (QuantitativeArithmeticRetainedExpressionIteration.unit A P) m=
      holomorphicSum u m) :
    let U := holomorphicSum (QuantitativeArithmeticRetainedExpressionIteration.unit A P) m
    let G := holomorphicSum (actualGramExpressions A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n u j) m
    U*G=G ∧ G*U=G := by
  let rows := actualReplacementRows A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n j
  exact physical_combined_support rows.baseline rows.prime _ u m _
    (QuantitativeArithmeticRetainedExpressionIteration.unit_physical_projection A P m) hu

#print axioms actualGramExpressions_physical_order
#print axioms actualGramExpressions_physical_support
end QuantitativeArithmeticRetainedIteration

namespace QuantitativeArithmeticRetainedIteration
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeEulerEndpointPrepared QuantitativeHolomorphic AsymptoticFiniteBranch
open QuantitativeEulerEndpointExponentialParameters QuantitativeEulerEndpointBernstein
open scoped Classical MatrixGroups
variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime)
    (e : Sector N) (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

/-- Partial iteration at a fixed horizon n: the block family and the
common reconstruction are held fixed while the iteration index varies. -/
def actualFinitePrefix (n : ℕ) (s : ℝ) (q : ℕ → ℝ[X]) (j : ℕ) : Expression :=
  let b := actualBlock A P hR₀ hN excluded threshold e S hS W B Bg D H₀ G C Kobs n
  let E := QuantitativeArithmeticRetainedCommonExpression.expression A P hR₀ (NeZero.pos N) s e
  QuantitativeArithmeticRetainedExpressionIteration.iterate A P
    (actualGramExpressions A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n E)
    (fun i => power (effortAt A P hR₀ e n b i)) q j

theorem actualFinitePrefix_physical_order (n j h : ℕ) (s : ℝ) (q : ℕ → ℝ[X])
    (hq : ∀ i<j,ScalarSharpening (q i)) :
    let U := holomorphicSum (QuantitativeArithmeticRetainedExpressionIteration.unit A P) (h+1)
    let F := holomorphicSum (actualFinitePrefix A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n s q j) (h+1)
    0≤F ∧ F≤1 ∧ F≤U ∧ U*F=F ∧ F*U=F := by
  apply QuantitativeArithmeticRetainedExpressionIteration.physical_order A P _ _ q j (h+1) _ hq
  intro i _
  have ho := actualGramExpressions_physical_order A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n i (h+1)
    _ (QuantitativeArithmeticRetainedCommonExpression.physical_norm A P hR₀ (NeZero.pos N) s e (h+1))
  have hs := actualGramExpressions_physical_support A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n i (h+1)
    _ (QuantitativeArithmeticRetainedCommonExpression.physical_right_terminal A P hR₀ (NeZero.pos N) s e h)
  exact ⟨ho.1,ho.2,hs⟩

/-- The literal finite filter from the regular approximation theorem is
also a positive contraction supported on the entire physical terminal
source. All actual Gram hypotheses have been discharged. -/
theorem actualFiniteExpression_physical_order (n h : ℕ) (s : ℝ) (q : ℕ → ℝ[X])
    (hq : ∀ j<n,ScalarSharpening (q j)) :
    let U := holomorphicSum (QuantitativeArithmeticRetainedExpressionIteration.unit A P) (h+1)
    let F := holomorphicSum (actualFiniteExpression A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n s q) (h+1)
    0≤F ∧ F≤1 ∧ F≤U ∧ U*F=F ∧ F*U=F :=
  actualFinitePrefix_physical_order A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n n h s q hq

#print axioms actualFinitePrefix_physical_order
#print axioms actualFiniteExpression_physical_order
end QuantitativeArithmeticRetainedIteration

namespace QuantitativeArithmeticRetainedExpressionIteration
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticFiniteBranch QuantitativeHolomorphic Polynomial
open QuantitativeEulerEndpointBernstein QuantitativeEulerEndpointResidual
variable {N Q : ℕ} {R₀ : Finset ℕ} {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (P : Parameters A)

/-- Approximate preservation of a terminal-supported operator under the
full-terminal finite recurrence. The initial identity incurs zero error. -/
theorem physical_residual (g : ℕ → Expression) (L : ℕ → ℕ) (q : ℕ → ℝ[X]) (n m : ℕ)
    (E : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)
    (hPE : holomorphicSum (unit A P) m*E=E)
    (hg : ∀ j<n,let U := holomorphicSum (unit A P) m
      let G := holomorphicSum (g j) m
      0≤G ∧ G≤1 ∧ U*G=G ∧ G*U=G)
    (hq : ∀ j<n,ScalarSharpening (q j))
    {δ : ℝ} (hδ : 0≤δ) (hgE : ∀ j<n,‖holomorphicSum (g j) m*E‖≤δ) :
    ‖holomorphicSum (iterate A P g L q n) m*E-E‖≤errorBudget L q n*δ := by
  induction n with
  | zero =>
    change ‖holomorphicSum (unit A P) m*E-E‖≤1*δ
    rw [hPE,sub_self,norm_zero,one_mul]
    exact hδ
  | succ n ih =>
    have hgn := hg n (by omega)
    have ho := physical_order A P g L q n m (fun j hj => hg j (by omega))
      (fun j hj => hq j (by omega))
    have hu := unit_physical_order A P m
    have he := ih (fun j hj => hg j (by omega)) (fun j hj => hq j (by omega))
      (fun j hj => hgE j (by omega))
    rw [physical_step]
    exact (QuantitativeEulerEndpointPhysicalCorner.sharpened_residual _ _ _ E
      (unit_physical_projection A P m) hu.1 hu.2 ho.2.2.2.1 ho.2.2.2.2
      hgn.2.2.1 hgn.2.2.2 ho.1 ho.2.1 hgn.1 hgn.2.1 hPE (L n) (q n) (hq n (by omega)).2.1).trans
      (errorBudget_step L q n hδ he (hgE n (by omega)))

#print axioms physical_residual
end QuantitativeArithmeticRetainedExpressionIteration

namespace QuantitativeArithmeticRetainedIteration
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeHolomorphic AsymptoticFiniteBranch QuantitativeEulerEndpointBernstein
open QuantitativeEulerEndpointExponentialParameters QuantitativeEulerEndpointResidual
open scoped MatrixGroups
variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime)
    (e : Sector N) (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

theorem actualFiniteExpression_physical_residual (n h : ℕ) (s : ℝ) (q : ℕ → ℝ[X])
    (hq : ∀ j<n,ScalarSharpening (q j))
    (E : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)
    (hPE : holomorphicSum (QuantitativeArithmeticRetainedExpressionIteration.unit A P) (h+1)*E=E)
    {δ : ℝ} (hδ : 0≤δ)
    (hgE : ∀ j<n,‖holomorphicSum (actualGramExpressions A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n
      (QuantitativeArithmeticRetainedCommonExpression.expression A P hR₀ (NeZero.pos N) s e) j) (h+1)*E‖≤δ) :
    ‖holomorphicSum (actualFiniteExpression A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n s q) (h+1)*E-E‖≤
      errorBudget (fun j => power (effortAt A P hR₀ e n
        (actualBlock A P hR₀ hN excluded threshold e S hS W B Bg D H₀ G C Kobs n) j)) q n*δ := by
  apply QuantitativeArithmeticRetainedExpressionIteration.physical_residual A P _ _ q n (h+1) E hPE _ hq hδ hgE
  intro j _
  have ho := actualGramExpressions_physical_order A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n j (h+1)
    _ (QuantitativeArithmeticRetainedCommonExpression.physical_norm A P hR₀ (NeZero.pos N) s e (h+1))
  have hs := actualGramExpressions_physical_support A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n j (h+1)
    _ (QuantitativeArithmeticRetainedCommonExpression.physical_right_terminal A P hR₀ (NeZero.pos N) s e h)
  exact ⟨ho.1,ho.2,hs⟩

#print axioms actualFiniteExpression_physical_residual
end QuantitativeArithmeticRetainedIteration

namespace QuantitativeArithmeticRetainedIteration
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeEulerEndpointPrepared QuantitativeHolomorphic AsymptoticFiniteBranch
open QuantitativeEulerEndpointPhysicalNormalization QuantitativeEulerEndpointBernstein
open QuantitativeEulerEndpointResidual QuantitativeEulerEndpointExponentialParameters
open ContinuousLinearMap
open scoped Classical MatrixGroups
variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime)
    (e : Sector N) (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

/-- Original physical row annihilation controls the selected finite Gram,
with only the common reconstruction error and no row-count loss. -/
theorem actualGramExpressions_original_residual (n j m : ℕ) (u : Expression)
    (V E : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)
    (hu : ‖holomorphicSum u m‖≤1) (hV : ‖V‖≤1)
    (hbase : let b := actualBlock A P hR₀ hN excluded threshold e S hS W B Bg D H₀ G C Kobs n j
      ∀ i,holomorphicSum (originalBaselineExpression N e b.compact
        P.epsilon_pos
        ((QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P)+4) i) m*V*E=0)
    (hprime : let b := actualBlock A P hR₀ hN excluded threshold e S hS W B Bg D H₀ G C Kobs n j
      ∀ i : Fin b.primes.length,holomorphicSum (originalPacketSequenceExpression b.compact
        P.epsilon_pos N (NeZero.pos N) (sign e.1)
        ((QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P)+4) b.primes i) m*V*E=0) :
    ‖holomorphicSum (actualGramExpressions A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n u j) m*E‖≤
      2*‖holomorphicSum u m-V‖*‖E‖ := by
  let rows := actualReplacementRows A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n j
  let T := holomorphicSum (actualGramExpressions A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n [identity] j) m
  have hi : holomorphicSum [identity] m=1 := by
    simp only [holomorphicSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,holomorphic_identity,add_zero]
  have ht := actualGramExpressions_physical_order A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs
    n j m [identity] (by
      rw [hi]
      exact ContinuousLinearMap.norm_id_le)
  have hn : ‖T‖≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ ht.1).mpr ht.2
  have he : holomorphicSum (actualGramExpressions A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n u j) m=
      star (holomorphicSum u m)*T*holomorphicSum u m := holomorphic_combined_compression rows.baseline rows.prime _ u m
  have hz : (star V*T*V)*E=0 := by
    change (star V*holomorphicSum (combinedGramExpression rows.baseline rows.prime _ [identity]) m*V)*E=0
    rw [rows.physical,holomorphic_combinedGramExpression]
    simp only [hi,mul_one]
    exact original_gram_kills _ _ _ V E hbase hprime
  rw [he]
  exact compression_residual T _ V E hn hu hV hz

end QuantitativeArithmeticRetainedIteration

namespace QuantitativeArithmeticRetainedIteration
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeEulerEndpointPrepared QuantitativeHolomorphic AsymptoticFiniteBranch
open QuantitativeEulerEndpointBernstein QuantitativeEulerEndpointResidual
open QuantitativeEulerEndpointExponentialParameters QuantitativeEulerEndpointNestedPerturbation
open QuantitativeArithmeticRetainedCommonExpression
open scoped Classical MatrixGroups
variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime)
    (e : Sector N) (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

/-- Explicit original equations after the EXACT normalized reconstruction.
No filter or counting conclusion is part of these premises. -/
structure OriginalPhysicalSolution (n h : ℕ)
    (E : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space) : Prop where
  terminal : holomorphicSum (QuantitativeArithmeticRetainedExpressionIteration.unit A P) (h+1)*E=E
  baseline : ∀ j<n,
    let b := actualBlock A P hR₀ hN excluded threshold e S hS W B Bg D H₀ G C Kobs n j
    ∀ i,holomorphicSum (originalBaselineExpression N e b.compact
      P.epsilon_pos
      ((QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P)+4) i) (h+1)*physicalExact A P hR₀ (NeZero.pos N) h e*E=0
  prime : ∀ j<n,
    let b := actualBlock A P hR₀ hN excluded threshold e S hS W B Bg D H₀ G C Kobs n j
    ∀ i : Fin b.primes.length,holomorphicSum (originalPacketSequenceExpression b.compact
      P.epsilon_pos N (NeZero.pos N) (sign e.1)
      ((QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P)+4) b.primes i) (h+1)*physicalExact A P hR₀ (NeZero.pos N) h e*E=0

theorem actualFiniteExpression_original_residual (n h : ℕ) (s : ℝ) (q : ℕ → ℝ[X])
    (hq : ∀ j<n,ScalarSharpening (q j))
    (E : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)
    (hsol : OriginalPhysicalSolution A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n h E) :
    ‖holomorphicSum (actualFiniteExpression A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n s q) (h+1)*E-E‖≤
      errorBudget (fun j => power (effortAt A P hR₀ e n
        (actualBlock A P hR₀ hN excluded threshold e S hS W B Bg D H₀ G C Kobs n) j)) q n*
          (Real.exp (-8*s)*‖E‖) := by
  apply actualFiniteExpression_physical_residual A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs
    n h s q hq E hsol.terminal (mul_nonneg (Real.exp_pos _).le (norm_nonneg E))
  intro j hj
  have hh := actualGramExpressions_original_residual A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs
    n j (h+1) (expression A P hR₀ (NeZero.pos N) s e) (physicalExact A P hR₀ (NeZero.pos N) h e) E
    (physical_norm A P hR₀ (NeZero.pos N) s e (h+1)) (physicalExact_norm A P hR₀ (NeZero.pos N) h e)
    (hsol.baseline j hj) (hsol.prime j hj)
  have he := physical_error A P hR₀ (NeZero.pos N) s e h
  change ‖holomorphicSum (expression A P hR₀ (NeZero.pos N) s e) (h+1)-physicalExact A P hR₀ (NeZero.pos N) h e‖≤Real.exp (-8*s)/2 at he
  apply hh.trans
  have hb : 2*‖holomorphicSum (expression A P hR₀ (NeZero.pos N) s e) (h+1)-physicalExact A P hR₀ (NeZero.pos N) h e‖≤
      Real.exp (-8*s) := by linarith
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg E)

/-- The same accuracy that pays the regular comparison budget pays the
physical original-equation residual; no new row-count factor appears. -/
theorem actualFiniteExpression_original_paid (n h : ℕ) {K : ℝ} (hK : 0≤K) (q : ℕ → ℝ[X])
    (hq : ∀ j<n,ScalarSharpening (q j))
    (hbudget : comparisonBudget (fun j => power (effortAt A P hR₀ e n
      (actualBlock A P hR₀ hN excluded threshold e S hS W B Bg D H₀ G C Kobs n) j)) q n≤Real.exp (Real.exp (K*(4:ℝ)^n)))
    (E : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)
    (hsol : OriginalPhysicalSolution A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n h E) :
    ‖holomorphicSum (actualFiniteExpression A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n
      (Real.exp ((K+1)*(4:ℝ)^n)) q) (h+1)*E-E‖≤(2/(4:ℝ)^n)*‖E‖ := by
  have he := actualFiniteExpression_original_residual A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs
    n h (Real.exp ((K+1)*(4:ℝ)^n)) q hq E hsol
  have hb := (errorBudget_le_comparisonBudget _ q n).trans hbudget
  have hp := QuantitativeEulerEndpointCommonReconstruction.amplified_error_le hK (one_le_pow₀ (by norm_num : (1:ℝ)≤4) (n:=n)) hb
  have hp' : errorBudget (fun j => power (effortAt A P hR₀ e n
      (actualBlock A P hR₀ hN excluded threshold e S hS W B Bg D H₀ G C Kobs n) j)) q n*
      Real.exp (-8*Real.exp ((K+1)*(4:ℝ)^n))≤2/(4:ℝ)^n := by
    rw [show (2:ℝ)/(4:ℝ)^n=2*(1/(4:ℝ)^n) by ring]
    nlinarith only [hp]
  rw [←mul_assoc] at he
  exact he.trans (mul_le_mul_of_nonneg_right hp' (norm_nonneg E))

#print axioms actualFiniteExpression_original_residual
#print axioms actualFiniteExpression_original_paid
end QuantitativeArithmeticRetainedIteration
