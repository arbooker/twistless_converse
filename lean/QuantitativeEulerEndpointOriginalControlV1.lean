module

public import QuantitativeEulerEndpointObservedStackV1

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

def fixedPrimeStack (N : ℕ) [NeZero N] (w : ℂ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :=
  stack (fun a : UnitResidue N => twist N (primeLift N a).q (NeZero.pos N)
    (primeLift N a).prime.pos w hs hε t x)

theorem fixedPrimeStack_component (N : ℕ) [NeZero N] (a : UnitResidue N)
    (w : ℂ) {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε)
    (t : ℕ) (x : ℍ) (v : Space) :
    ‖twist N (primeLift N a).q (NeZero.pos N) (primeLift N a).prime.pos w hs hε t x v‖^2≤
      ‖fixedPrimeStack N w hs hε t x v‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.single_le_sum (fun b _ => sq_nonneg
    ‖twist N (primeLift N b).q (NeZero.pos N) (primeLift N b).prime.pos w hs hε t x v‖)
    (Finset.mem_univ a)

/-- A quantitative local observation estimate for one actual integral
matrix residual and a fixed right label. All operators in its energy are
literal original observations or the actual shifted fresh-prime stack. -/
def OriginalControl {N : ℕ} [NeZero N] {excluded : Finset ℕ} {threshold : ℕ}
    (P : Prepared N excluded threshold) (γ : SL(2,ℤ)) (g : G) (B K : ℝ) : Prop :=
  ∀ (C : ℝ), B≤C → ∀ (q : ℕ) [Fact q.Prime], P.Good q →
    ∃ hqN : ¬q∣N, ∀ (w : ℂ) (_hw : w*w=1)
      {s : Set ℍ} (hs : IsCompact s) {ε Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
      (_hre : ∀ z∈s, |z.re|≤1) (_hlo : ∀ z∈s, Y≤z.im) (_him : ∀ z∈s, z.im≤H)
      (t : ℕ) (x : ℍ) (v : Space),
    let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
    ‖compactAction hs hε t x ((symbol (integralLabel γ)-1)*symbol g) v‖^2≤
    K*((integerCompactDistortion L H)^t)^2*
      (‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w (freshObservationRegion_compact L H hY) hε t x v‖^2+
        ‖fixedPrimeStack N w (freshObservationRegion_compact L H hY) hε t x v‖^2+
        ‖stack (fun i => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
          (freshObservationRegion_compact L H hY) hε t i x) v‖^2)

theorem observed_matrix_original_control {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (a : UnitResidue N) (g : G) :
    ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧ OriginalControl P (observedPrimeMatrix N a) g B K := by
  obtain ⟨B,hB,K,hK,hbound⟩ := observed_matrix_stack_bound P a g
  refine ⟨B,hB,K,hK,?_⟩
  intro C hBC q hqPrime hqGood
  obtain ⟨hqN,hqbound⟩ := hbound C hBC q hqGood
  refine ⟨hqN,?_⟩
  intro w hw s hs ε Y H hε hY hre hlo him t x v
  exact (hqbound w hw hs hε hY hre hlo him t x v).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (le_refl _) (fixedPrimeStack_component N a w _ hε t x v)) (le_refl _))
      (mul_nonneg hK (sq_nonneg _)))

theorem gamma1_original_control {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma1 N) (g : G) :
    ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧ OriginalControl P γ g B K := by
  obtain ⟨B,hB,K,hK,hbound⟩ := gamma1_fixed_multiplier_stack_bound P γ hγ (symbol g)
  refine ⟨B,hB,K,hK,?_⟩
  intro C hBC q hqPrime hqGood
  obtain ⟨hqN,hqbound⟩ := hbound C hBC q hqGood
  refine ⟨hqN,?_⟩
  intro w hw s hs ε Y H hε hY hre hlo him t x v
  apply (hqbound w hw hs hε hY hre hlo him t x v).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK (sq_nonneg _))
  exact add_le_add (le_add_of_nonneg_right (sq_nonneg _)) (le_refl _)

#print axioms fixedPrimeStack_component
#print axioms observed_matrix_original_control
#print axioms gamma1_original_control
end QuantitativeEulerEndpointPrepared
