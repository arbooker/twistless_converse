module

public import QuantitativeEulerEndpointGeneratorHeightV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix UpperHalfPlane QuantitativeArithmetic QuantitativeHolomorphic
open QuantitativeEulerDensityGenerators QuantitativeEulerDiamondDecode
open AsymptoticCongruenceLabels AsymptoticRegularObservationRows
open AsymptoticRegularCompactBranch (Space)
open AsymptoticObservationStack
open scoped Classical MatrixGroups

theorem matrix_generator_recovery {E : Type*} [AddCommGroup E]
    (N : ℕ) [NeZero N] (a : UnitResidue N) (γ : Generator N) (F : MatrixAlgebra →+ E) :
    F (matrixSymbol γ.val.val-1)=
      F (matrixSymbol (family N a (some γ)).val-1)-
      F ((matrixSymbol (family N a none).val-1)*matrixSymbol γ.val.val) := by
  have h := generator_defect N a γ F
  change F (matrixSymbol γ.val.val)-F 1=
    (F (matrixSymbol (family N a (some γ)).val)-F 1)-
    (F (matrixSymbol (family N a none).val*matrixSymbol γ.val.val)-F (1*matrixSymbol γ.val.val)) at h
  simpa only [sub_mul,map_sub,one_mul] using h

theorem matrix_compact_congruence (γ : SL(2,ℤ)) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    matrixCompactAction hs hε t x (matrixSymbol γ.val-1)=
      AsymptoticCongruenceDefect.operator γ hs hε t x := by
  have h := matrixCompactAction_integral_defect hs hε t x γ 1
  have hm : matrixSymbol (1 : SL(2,ℤ)).val=1 := rfl
  have hg : symbol (integralLabel (1 : SL(2,ℤ)))=1 := by rw [map_one,map_one]
  rw [hm,mul_one,hg,mul_one,compactAction_congruence] at h
  exact h

private theorem two_residuals_squared (u v : Space) (K : ℝ)
    (hu : ‖u‖^2≤50*K) (hv : ‖v‖^2≤50*K) : ‖u-v‖^2≤200*K := by
  have h := (sq_le_sq₀ (norm_nonneg (u-v)) (add_nonneg (norm_nonneg u) (norm_nonneg v))).2
    (norm_sub_le u v)
  nlinarith [sq_nonneg (‖u‖-‖v‖)]

/-- Every good prime controls EVERY fixed Gamma1 generator through two
members of its own residue family. The coefficient and observation region
are uniform over that generator set and over the residue of the prime. -/
theorem good_prime_generator_stack_bound {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (q : ℕ) [Fact q.Prime] (hqGood : P.Good q) :
    ∃ hqN : ¬q∣N, ∀ (γ : Generator N) (w : ℂ) (_hw : w*w=1)
      {s : Set ℍ} (hs : IsCompact s) {ε Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
      (_hre : ∀ z∈s, |z.re|≤1) (_hlo : ∀ z∈s, Y≤z.im) (_him : ∀ z∈s, z.im≤H)
      (t : ℕ) (x : ℍ) (v : Space),
    let L := generatorTransportConstant P*(q : ℝ)^4
    ‖AsymptoticCongruenceDefect.operator γ.val hs hε t x v‖^2≤
    200*((integerCompactDistortion L H)^t)^2*
      (‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w (freshObservationRegion_compact L H hY) hε t x v‖^2+
        ‖stack (fun j => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
          (freshObservationRegion_compact L H hY) hε t j x) v‖^2) := by
  obtain ⟨_hex,hqN,_hthreshold,a,_hqa,hcert⟩ := P.prime_data q Fact.out hqGood
  refine ⟨hqN,?_⟩
  intro γ w hw s hs ε Y H hε hY hre hlo him t x v
  let L := generatorTransportConstant P*(q : ℝ)^4
  have hB : 0≤generatorHeight N := zero_le_one.trans (generatorHeight_one_le N)
  obtain ⟨ds,⟨cs⟩⟩ := hcert (some γ)
  obtain ⟨dn,⟨cn⟩⟩ := hcert none
  have hsbound := compact_prime_right_stack_of_height P a (some γ) cs hqN 1
    hB (generatorHeight_identity N) L (generator_transport_height P a (some γ) q)
    w hw hs hε hY hre hlo him t x v
  have hnbound := compact_prime_right_stack_of_height P a none cn hqN γ.val
    hB (generatorHeight_bound N γ) L (generator_transport_height P a none q)
    w hw hs hε hY hre hlo him t x v
  have hm : matrixSymbol (1 : SL(2,ℤ)).val=1 := rfl
  rw [hm,mul_one] at hsbound
  have he := congrArg (fun T : Space →L[ℂ] Space => T v)
    (matrix_generator_recovery N a γ (matrixCompactAction hs hε t x))
  rw [matrix_compact_congruence,_root_.sub_apply] at he
  rw [he]
  have htotal := two_residuals_squared _ _ _
    (hsbound.trans_eq (mul_assoc _ _ _)) (hnbound.trans_eq (mul_assoc _ _ _))
  exact htotal.trans_eq (mul_assoc _ _ _).symm

#print axioms matrix_generator_recovery
#print axioms matrix_compact_congruence
#print axioms good_prime_generator_stack_bound
end QuantitativeEulerEndpointPrepared
