module

public import QuantitativeEulerEndpointGamma0CheckV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix UpperHalfPlane QuantitativeArithmetic QuantitativeHolomorphic
open QuantitativeEulerDensityGenerators QuantitativeEulerDiamondDecode
open AsymptoticCongruenceLabels AsymptoticRegularObservationRows AsymptoticObservationStack
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups

theorem original_control_one {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold) (g : G) :
    OriginalControl P 1 g 1 0 := by
  intro C _hC q hqPrime hqGood
  obtain ⟨_hex,hqN,_ht,_a,_hqa,_hcert⟩ := P.prime_data q Fact.out hqGood
  refine ⟨hqN,?_⟩
  intro w _hw s hs ε Y H hε hY _hre _hlo _him t x v
  simp only [map_one,sub_self,zero_mul,map_zero,_root_.zero_apply,norm_zero]
  norm_num

theorem original_control_inverse {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} {P : Prepared N excluded threshold}
    (γ : SL(2,ℤ)) (g : G) {B K : ℝ}
    (h : OriginalControl P γ (integralLabel γ⁻¹*g) B K) :
    OriginalControl P γ⁻¹ g B K := by
  intro C hBC q hqPrime hqGood
  obtain ⟨hqN,hqbound⟩ := h C hBC q hqGood
  refine ⟨hqN,?_⟩
  intro w hw s hs ε Y H hε hY hre hlo him t x v
  have he := congrArg (fun a : ℝ => a^2) (projective_inverse_letter_norm γ⁻¹ g hs hε t x v)
  simp only [inv_inv] at he
  exact he.trans_le (hqbound w hw hs hε hY hre hlo him t x v)

theorem two_vector_squared (u v : Space) : ‖u+v‖^2≤2*(‖u‖^2+‖v‖^2) := by
  have h := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2
    (norm_add_le u v)
  nlinarith only [h,sq_nonneg (‖u‖-‖v‖)]

theorem original_control_mul {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} {P : Prepared N excluded threshold}
    (α β : SL(2,ℤ)) (g : G) {B K₁ K₂ : ℝ}
    (hα : OriginalControl P α (integralLabel β*g) B K₁)
    (hβ : OriginalControl P β g B K₂) :
    OriginalControl P (α*β) g B (2*(K₁+K₂)) := by
  intro C hBC q hqPrime hqGood
  obtain ⟨hqN,hαq⟩ := hα C hBC q hqGood
  obtain ⟨_hqN,hβq⟩ := hβ C hBC q hqGood
  refine ⟨hqN,?_⟩
  intro w hw s hs ε Y H hε hY hre hlo him t x v
  let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
  let Q := ((integerCompactDistortion L H)^t)^2*
    (‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w (freshObservationRegion_compact L H hY) hε t x v‖^2+
      ‖fixedPrimeStack N w (freshObservationRegion_compact L H hY) hε t x v‖^2+
      ‖stack (fun i => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
        (freshObservationRegion_compact L H hY) hε t i x) v‖^2)
  let u := compactAction hs hε t x ((symbol (integralLabel α)-1)*symbol (integralLabel β*g)) v
  let z := compactAction hs hε t x ((symbol (integralLabel β)-1)*symbol g) v
  have hu : ‖u‖^2≤K₁*Q :=
    (hαq w hw hs hε hY hre hlo him t x v).trans_eq (mul_assoc _ _ _)
  have hz : ‖z‖^2≤K₂*Q :=
    (hβq w hw hs hε hY hre hlo him t x v).trans_eq (mul_assoc _ _ _)
  have halg : (symbol (integralLabel (α*β))-1)*symbol g=
      (symbol (integralLabel α)-1)*symbol (integralLabel β*g)+
        (symbol (integralLabel β)-1)*symbol g := by
    simp only [map_mul]
    noncomm_ring
  have he := congrArg (fun T : Space →L[ℂ] Space => T v)
    ((congrArg (compactAction hs hε t x) halg).trans (map_add (compactAction hs hε t x) _ _))
  simp only [_root_.add_apply] at he
  have ht := (two_vector_squared u z).trans
    (mul_le_mul_of_nonneg_left (add_le_add hu hz) (by norm_num : (0 : ℝ)≤2))
  exact (congrArg (fun a : Space => ‖a‖^2) he).trans_le
    (ht.trans_eq (by dsimp only [Q]; ring))

#print axioms original_control_one
#print axioms original_control_inverse
#print axioms original_control_mul
end QuantitativeEulerEndpointPrepared
