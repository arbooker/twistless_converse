module

public import QuantitativeEulerEndpointOriginalControlV1
public import QuantitativeEulerEndpointWideObservedStackV1


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

/-- A quantitative local observation estimate for one actual integral
matrix residual and a fixed right label. All operators in its energy are
literal original observations or the actual shifted fresh-prime stack. -/
def WideOriginalControl {N : ℕ} [NeZero N] {excluded : Finset ℕ} {threshold : ℕ}
    (P : Prepared N excluded threshold) (γ : SL(2,ℤ)) (g : G) (B K : ℝ) : Prop :=
  ∀ (C : ℝ), B≤C → ∀ (q : ℕ) [Fact q.Prime], P.Good q →
    ∃ hqN : ¬q∣N, ∀ (w : ℂ) (_hw : w*w=1)
      {s : Set ℍ} (hs : IsCompact s) {ε W₀ Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
      (_hre : ∀ z∈s, |z.re|≤W₀) (_hlo : ∀ z∈s, Y≤z.im) (_him : ∀ z∈s, z.im≤H)
      (t : ℕ) (x : ℍ) (v : Space),
    let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
    ‖compactAction hs hε t x ((symbol (integralLabel γ)-1)*symbol g) v‖^2≤
    K*((wideDistortion L W₀ H)^t)^2*
      (‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w (wideFreshRegion_compact L W₀ H hY) hε t x v‖^2+
        ‖fixedPrimeStack N w (wideFreshRegion_compact L W₀ H hY) hε t x v‖^2+
        ‖stack (fun i => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
          (wideFreshRegion_compact L W₀ H hY) hε t i x) v‖^2)

theorem wide_observed_matrix_original_control {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (a : UnitResidue N) (g : G) :
    ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧ WideOriginalControl P (observedPrimeMatrix N a) g B K := by
  obtain ⟨B,hB,K,hK,hbound⟩ := wide_observed_matrix_stack_bound P a g
  refine ⟨B,hB,K,hK,?_⟩
  intro C hBC q hqPrime hqGood
  obtain ⟨hqN,hqbound⟩ := hbound C hBC q hqGood
  refine ⟨hqN,?_⟩
  intro w hw s hs ε W₀ Y H hε hY hre hlo him t x v
  exact (hqbound w hw hs hε hY hre hlo him t x v).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (le_refl _) (fixedPrimeStack_component N a w _ hε t x v)) (le_refl _))
      (mul_nonneg hK (sq_nonneg _)))

theorem wide_gamma1_original_control {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma1 N) (g : G) :
    ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧ WideOriginalControl P γ g B K := by
  obtain ⟨B,hB,K,hK,hbound⟩ := wide_gamma1_fixed_multiplier_stack_bound P γ hγ (symbol g)
  refine ⟨B,hB,K,hK,?_⟩
  intro C hBC q hqPrime hqGood
  obtain ⟨hqN,hqbound⟩ := hbound C hBC q hqGood
  refine ⟨hqN,?_⟩
  intro w hw s hs ε W₀ Y H hε hY hre hlo him t x v
  apply (hqbound w hw hs hε hY hre hlo him t x v).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK (sq_nonneg _))
  exact add_le_add (le_add_of_nonneg_right (sq_nonneg _)) (le_refl _)

#print axioms wide_observed_matrix_original_control
#print axioms wide_gamma1_original_control
end QuantitativeEulerEndpointPrepared
