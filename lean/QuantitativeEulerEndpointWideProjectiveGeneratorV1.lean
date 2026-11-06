module

public import QuantitativeEulerEndpointProjectiveGeneratorV1
public import QuantitativeEulerEndpointWideProjectiveStackV1


set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix UpperHalfPlane QuantitativeArithmetic QuantitativeHolomorphic
open QuantitativeEulerDensityGenerators QuantitativeEulerDiamondDecode
open AsymptoticCongruenceLabels AsymptoticRegularObservationRows
open AsymptoticRationalBranches AsymptoticRationalFreeness
open AsymptoticRegularCompactBranch (Space)
open AsymptoticObservationStack
open scoped Classical MatrixGroups

private theorem projective_two_residuals_squared (u v : Space) (K : ℝ)
    (hu : ‖u‖^2≤50*K) (hv : ‖v‖^2≤50*K) : ‖u-v‖^2≤200*K := by
  have h := (sq_le_sq₀ (norm_nonneg (u-v)) (add_nonneg (norm_nonneg u) (norm_nonneg v))).2
    (norm_sub_le u v)
  nlinarith [sq_nonneg (‖u‖-‖v‖)]

/-- Actual Gamma1 generator recovery with any projective right action.
The prime is chosen independently of the generator and the right label;
the same explicit bound applies to every integral representative of height B. -/
theorem wide_good_prime_projective_generator_stack_bound {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (q : ℕ) [Fact q.Prime] (hqGood : P.Good q) :
    ∃ hqN : ¬q∣N, ∀ (γ : Generator N) (g : G) (M : IntegerMatrix2) (B : ℝ)
      (_hM : IntegerAction g M) (_hB : 0≤B) (_hb : MatrixEntryBound M B) (w : ℂ) (_hw : w*w=1)
      {s : Set ℍ} (hs : IsCompact s) {ε W₀ Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
      (_hre : ∀ z∈s, |z.re|≤W₀) (_hlo : ∀ z∈s, Y≤z.im) (_him : ∀ z∈s, z.im≤H)
      (t : ℕ) (x : ℍ) (v : Space),
    let L := (2*generatorTransportConstant P*B)*(q : ℝ)^4
    ‖compactAction hs hε t x ((symbol (integralLabel γ.val)-1)*symbol g) v‖^2≤
    200*((wideDistortion L W₀ H)^t)^2*
      (‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w (wideFreshRegion_compact L W₀ H hY) hε t x v‖^2+
        ‖stack (fun j => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
          (wideFreshRegion_compact L W₀ H hY) hε t j x) v‖^2) := by
  obtain ⟨_hex,hqN,_hthreshold,a,_hqa,hcert⟩ := P.prime_data q Fact.out hqGood
  refine ⟨hqN,?_⟩
  intro γ g M B hM hB hb w hw s hs ε W₀ Y H hε hY hre hlo him t x v
  let L := (2*generatorTransportConstant P*B)*(q : ℝ)^4
  let R := 2*generatorHeight N*B
  have hG : 0≤generatorHeight N := zero_le_one.trans (generatorHeight_one_le N)
  have hR : 0≤R := mul_nonneg (mul_nonneg (by norm_num) hG) hB
  have hbR : MatrixEntryBound M R := by
    apply entry_bound_mono hb
    have h := mul_le_mul_of_nonneg_right
      (show (1 : ℝ)≤2*generatorHeight N by linarith [generatorHeight_one_le N]) hB
    simpa only [one_mul] using h
  have hγM : IntegerAction (integralLabel γ.val*g) (γ.val.val*M) :=
    (integerAction_integralLabel γ.val).mul hM
  have hγMb : MatrixEntryBound (γ.val.val*M) R :=
    matrix_entry_bound_mul hG (generatorHeight_bound N γ) hb
  obtain ⟨ds,⟨cs⟩⟩ := hcert (some γ)
  obtain ⟨dn,⟨cn⟩⟩ := hcert none
  have hsbound := wide_projective_prime_stack_of_height P a (some γ) cs hqN g
    hM hR hbR L (projective_generator_height P a (some γ) q hB)
    w hw hs hε hY hre hlo him t x v
  have hnbound := wide_projective_prime_stack_of_height P a none cn hqN (integralLabel γ.val*g)
    hγM hR hγMb L (projective_generator_height P a none q hB)
    w hw hs hε hY hre hlo him t x v
  have he := congrArg (fun T : Space →L[ℂ] Space => T v)
    (projective_generator_recovery N a γ g hs hε t x)
  rw [_root_.sub_apply] at he
  rw [he]
  have htotal := projective_two_residuals_squared _ _ _
    (hsbound.trans_eq (mul_assoc _ _ _)) (hnbound.trans_eq (mul_assoc _ _ _))
  exact htotal.trans_eq (mul_assoc _ _ _).symm

#print axioms wide_good_prime_projective_generator_stack_bound
end QuantitativeEulerEndpointPrepared
