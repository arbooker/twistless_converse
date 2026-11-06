module

public import QuantitativeEulerEndpointGeneratorStackV1

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

theorem matrix_generator_recovery_right {E : Type*} [AddCommGroup E]
    (N : ℕ) [NeZero N] (a : UnitResidue N) (γ : Generator N)
    (β : SL(2,ℤ)) (F : MatrixAlgebra →+ E) :
    F ((matrixSymbol γ.val.val-1)*matrixSymbol β.val)=
      F ((matrixSymbol (family N a (some γ)).val-1)*matrixSymbol β.val)-
      F ((matrixSymbol (family N a none).val-1)*matrixSymbol (γ.val*β).val) := by
  have h := matrix_generator_recovery N a γ (rightTranslate F β.val)
  change F ((matrixSymbol γ.val.val-1)*matrixSymbol β.val)=
    F ((matrixSymbol (family N a (some γ)).val-1)*matrixSymbol β.val)-
    F (((matrixSymbol (family N a none).val-1)*matrixSymbol γ.val.val)*matrixSymbol β.val) at h
  have hm : matrixSymbol (γ.val*β).val=matrixSymbol γ.val.val*matrixSymbol β.val :=
    matrixSymbol_mul _ _
  rw [hm,←mul_assoc]
  exact h

private theorem generator_right_height {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (a : UnitResidue N) (i : Option (Generator N)) (q : ℕ) {B : ℝ} (hB : 0≤B) :
    2*(localTransportConstant P a i*(q : ℝ)^4)*(2*generatorHeight N*B)≤
      (2*generatorTransportConstant P*B)*(q : ℝ)^4 := by
  have h := mul_le_mul_of_nonneg_right (generator_transport_height P a i q)
    (mul_nonneg (by norm_num : (0 : ℝ)≤2) hB)
  convert h using 1 <;> ring

private theorem two_right_residuals_squared (u v : Space) (K : ℝ)
    (hu : ‖u‖^2≤50*K) (hv : ‖v‖^2≤50*K) : ‖u-v‖^2≤200*K := by
  have h := (sq_le_sq₀ (norm_nonneg (u-v)) (add_nonneg (norm_nonneg u) (norm_nonneg v))).2
    (norm_sub_le u v)
  nlinarith [sq_nonneg (‖u‖-‖v‖)]

/-- The same fresh prime controls every fixed generator after any integral
right multiplier, with an explicit extra linear factor in its height.
This permits later word suffixes without assumptions on translated strips. -/
theorem good_prime_generator_right_stack_bound {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (q : ℕ) [Fact q.Prime] (hqGood : P.Good q) :
    ∃ hqN : ¬q∣N, ∀ (γ : Generator N) (β : SL(2,ℤ)) (B : ℝ)
      (_hB : 0≤B) (_hβ : MatrixEntryBound β.val B) (w : ℂ) (_hw : w*w=1)
      {s : Set ℍ} (hs : IsCompact s) {ε Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
      (_hre : ∀ z∈s, |z.re|≤1) (_hlo : ∀ z∈s, Y≤z.im) (_him : ∀ z∈s, z.im≤H)
      (t : ℕ) (x : ℍ) (v : Space),
    let L := (2*generatorTransportConstant P*B)*(q : ℝ)^4
    ‖compactAction hs hε t x
      ((symbol (integralLabel γ.val)-1)*symbol (integralLabel β)) v‖^2≤
    200*((integerCompactDistortion L H)^t)^2*
      (‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w (freshObservationRegion_compact L H hY) hε t x v‖^2+
        ‖stack (fun j => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
          (freshObservationRegion_compact L H hY) hε t j x) v‖^2) := by
  obtain ⟨_hex,hqN,_hthreshold,a,_hqa,hcert⟩ := P.prime_data q Fact.out hqGood
  refine ⟨hqN,?_⟩
  intro γ β B hB hβ w hw s hs ε Y H hε hY hre hlo him t x v
  let L := (2*generatorTransportConstant P*B)*(q : ℝ)^4
  let R := 2*generatorHeight N*B
  have hG : 0≤generatorHeight N := zero_le_one.trans (generatorHeight_one_le N)
  have hR : 0≤R := mul_nonneg (mul_nonneg (by norm_num) hG) hB
  have hβR : MatrixEntryBound β.val R := by
    apply entry_bound_mono hβ
    have h := mul_le_mul_of_nonneg_right
      (show (1 : ℝ)≤2*generatorHeight N by linarith [generatorHeight_one_le N]) hB
    simpa only [one_mul] using h
  have hγβR : MatrixEntryBound (γ.val*β).val R :=
    matrix_entry_bound_mul hG (generatorHeight_bound N γ) hβ
  obtain ⟨ds,⟨cs⟩⟩ := hcert (some γ)
  obtain ⟨dn,⟨cn⟩⟩ := hcert none
  have hsbound := compact_prime_right_stack_of_height P a (some γ) cs hqN β
    hR hβR L (generator_right_height P a (some γ) q hB)
    w hw hs hε hY hre hlo him t x v
  have hnbound := compact_prime_right_stack_of_height P a none cn hqN (γ.val*β)
    hR hγβR L (generator_right_height P a none q hB)
    w hw hs hε hY hre hlo him t x v
  have he := congrArg (fun T : Space →L[ℂ] Space => T v)
    (matrix_generator_recovery_right N a γ β (matrixCompactAction hs hε t x))
  rw [matrixCompactAction_integral_defect hs hε t x γ.val β,_root_.sub_apply] at he
  rw [he]
  have htotal := two_right_residuals_squared _ _ _
    (hsbound.trans_eq (mul_assoc _ _ _)) (hnbound.trans_eq (mul_assoc _ _ _))
  exact htotal.trans_eq (mul_assoc _ _ _).symm

#print axioms matrix_generator_recovery_right
#print axioms good_prime_generator_right_stack_bound
end QuantitativeEulerEndpointPrepared
