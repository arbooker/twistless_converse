module

public import QuantitativeEulerEndpointWideFamilyExpressionV1
public import QuantitativeEulerEndpointWideBaselineBoundsV1
public import QuantitativeEulerEndpointPacketGramV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane AsymptoticFiniteBranch QuantitativeHolomorphic
open AsymptoticRegularObservationRows AsymptoticCertificateBranches
open scoped Classical

variable {s : Set ℍ} (hs : IsCompact s) {ε R Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
    (hre : ∀ z∈s, |z.re|≤R) (hlo : ∀ z∈s, Y≤z.im) (hhi : ∀ z∈s, z.im≤H)

include hY hre hlo hhi in
theorem exists_twist_expression (N q : ℕ) (hN : 0<N) (hq : 0<q) (w : ℂ) (t : ℕ) :
    ∃ E : Expression,
      (∀ x, regularSum E x=twist N q hN hq w hs hε t x) ∧
      (∀ m, holomorphicSum E m=holomorphicSum (compactFamilyExpression (twistBranches N q hN hq)
        (Sum.elim (fun _ => (1:ℂ)) (fun _ => -w)) hs hε t) m) ∧
      expressionBound E≤wideTwistBound N q w R Y H t ∧
      ExpressionMatrixBound E (4*(1+(wideCompactCutoff (N*q^3:ℕ) R Y H:ℝ))*(N*q^3:ℕ)) := by
  choose M hM hb using twistBranches_integer_representatives N q hN hq
  let b := twistBranches N q hN hq
  let c := Sum.elim (fun _ : residues q => (1:ℂ)) (fun _ : residues q => -w)
  have hB : (0:ℝ)≤(N*q^3:ℕ) := by positivity
  let E := wideFamilyExpression b c hs M hM hB hb hY hε hre hlo hhi t
  refine ⟨E,wideFamily_regular b c hs M hM hB hb hY hε hre hlo hhi t,
    wideFamily_holomorphic b c hs M hM hB hb hY hε hre hlo hhi t,?_,
    wideFamily_matrix b c hs M hM hB hb hY hε hre hlo hhi t⟩
  rw [wideFamily_mass]
  exact mul_le_mul_of_nonneg_right (twist_coefficient_mass q w) (wideRowBound_nonneg _ _ _ _ _)

include hY hre hlo hhi in
theorem exists_ramified_expression (p : ℕ) (hp : 0<p) (δ : ℂ) (t : ℕ) :
    ∃ E : Expression,
      (∀ x, regularSum E x=bad p hp δ hs hε t x) ∧
      (∀ m, holomorphicSum E m=holomorphicSum (compactFamilyExpression (ramifiedBranches p hp)
        (Sum.elim (fun _ => (1:ℂ)) (fun _ => -δ)) hs hε t) m) ∧
      expressionBound E≤wideRamifiedBound p δ R Y H t ∧
      ExpressionMatrixBound E (4*(1+(wideCompactCutoff p R Y H:ℝ))*(p:ℝ)) := by
  choose M hM hb using ramifiedBranches_integer_representatives p hp
  let b := ramifiedBranches p hp
  let c := Sum.elim (fun _ : Fin p => (1:ℂ)) (fun _ : Unit => -δ)
  have hB : (0:ℝ)≤p := by positivity
  let E := wideFamilyExpression b c hs M hM hB hb hY hε hre hlo hhi t
  refine ⟨E,wideFamily_regular b c hs M hM hB hb hY hε hre hlo hhi t,
    wideFamily_holomorphic b c hs M hM hB hb hY hε hre hlo hhi t,?_,
    wideFamily_matrix b c hs M hM hB hb hY hε hre hlo hhi t⟩
  have hc : (∑ i, ‖c i‖)≤((p:ℝ)+1)*(1+‖δ‖) := by
    have hi (i : Fin p ⊕ Unit) : ‖c i‖≤1+‖δ‖ := by
      cases i <;> simp only [c,Sum.elim_inl,Sum.elim_inr,norm_one,norm_neg] <;> linarith [norm_nonneg δ]
    calc
      _ ≤ ∑ _i : Fin p ⊕ Unit, (1+‖δ‖) := Finset.sum_le_sum (fun i _ => hi i)
      _ = _ := by simp; ring
  rw [wideFamily_mass]
  exact mul_le_mul_of_nonneg_right hc (wideRowBound_nonneg _ _ _ _ _)

include hY hre hlo hhi in
theorem exists_packet_expression (N q : ℕ) [Fact q.Prime] (hN : 0<N) (w : ℂ) (t : ℕ) :
    ∃ E : Expression,
      (∀ x, regularSum E x=packetTwistRow N q hN w hs hε t x) ∧
      expressionBound E≤widePacketBound N q w R Y H t ∧
      ExpressionMatrixBound E (4*(1+(wideCompactCutoff (N*q^3:ℕ) R Y H:ℝ))*(N*q^3:ℕ)) := by
  obtain ⟨E,hE,_hphys,hmass,hmatrix⟩ := exists_twist_expression hs hε hY hre hlo hhi
    N q hN (Fact.out : q.Prime).pos w t
  let a : ℝ := -Real.sqrt (2*(q:ℝ))
  refine ⟨scaleExpression (a:ℂ) E,?_,?_,hmatrix.scale (a:ℂ)⟩
  · intro x
    rw [regularSum_scale,hE,packet_twist_row_eq]
    exact (RCLike.real_smul_eq_coe_smul (K:=ℂ) a (twist N q hN (Fact.out : q.Prime).pos w hs hε t x)).symm
  · have hq1 : (1:ℝ)≤q := by exact_mod_cast (Fact.out : q.Prime).one_le
    have hsq : Real.sqrt (2*(q:ℝ))≤2*(q:ℝ) := by
      have hh := Real.sqrt_le_sqrt (show 2*(q:ℝ)≤(2*(q:ℝ))^2 by nlinarith)
      simpa only [Real.sqrt_sq_eq_abs,abs_of_nonneg (show 0≤2*(q:ℝ) by positivity)] using hh
    rw [expressionBound_scale,Complex.norm_real,Real.norm_eq_abs]
    dsimp only [a]
    rw [abs_neg,abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      _ ≤ (2*(q:ℝ))*wideTwistBound N q w R Y H t := mul_le_mul hsq hmass
        (expressionBound_nonneg _) (by positivity)
      _ = _ := by unfold wideTwistBound widePacketBound wideRowBound; ring

#print axioms exists_twist_expression
#print axioms exists_ramified_expression
#print axioms exists_packet_expression
end QuantitativeEulerEndpointPrepared
