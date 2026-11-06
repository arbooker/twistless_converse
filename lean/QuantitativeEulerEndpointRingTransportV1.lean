module

public import QuantitativeEulerEndpointRecoveryRightV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane QuantitativeArithmetic QuantitativeHolomorphic
open QuantitativeEulerDiamondDecode AsymptoticRationalFreeness
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

/-- A fixed finite ring multiplier has one integral height and one scalar
mass, chosen before the left expression and all analytic cutoffs. Every
larger height is permitted, so separately composed multipliers can share
the same explicit rectangle. -/
theorem fixed_ring_common_bound (E : Ring) :
    ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ (C : ℝ), B≤C → ∀ (A : Ring) {s : Set ℍ} (hs : IsCompact s)
        {ε Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
        (_hre : ∀ z∈s, |z.re|≤1) (_hlo : ∀ z∈s, Y≤z.im) (_him : ∀ z∈s, z.im≤H)
        (t : ℕ) (x : ℍ) (v : Space),
      ‖compactAction hs hε t x (A*E) v‖≤
        K*(integerCompactDistortion C H)^t*
          ‖compactAction (commonImageRegion_compact C H hY) hε t x A v‖ := by
  let J := ↥E.coeff.support
  obtain ⟨B,hB,hmat⟩ := QuantitativeEulerIntegerHeight.finite_family_height
    (fun g : J => g.val)
  let K : ℝ := ∑ g : J, ‖E.coeff g.val‖
  refine ⟨B,hB,K,Finset.sum_nonneg (fun g _ => norm_nonneg _),?_⟩
  intro C hBC A s hs ε Y H hε hY hre hlo him t x v
  have hC : 0≤C := zero_le_one.trans (hB.trans hBC)
  let D := (integerCompactDistortion C H)^t*
    ‖compactAction (commonImageRegion_compact C H hY) hε t x A v‖
  have hrow (g : J) : ‖compactAction hs hε t x (A*symbol g.val) v‖≤D := by
    obtain ⟨M,hM,hMb⟩ := hmat g
    exact compact_right_common_bound g.val hM hC (entry_bound_mono hMb hBC) hY
      A hs hε hre hlo him t x v
  have hsum : ‖∑ g : J, E.coeff g.val • compactAction hs hε t x (A*symbol g.val) v‖≤K*D := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ g : J, ‖E.coeff g.val‖*D := by
        apply Finset.sum_le_sum
        intro g _
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hrow g) (norm_nonneg _)
      _ = K*D := (Finset.sum_mul _ _ _).symm
  rw [compact_expression_right_expand,_root_.sum_apply]
  exact hsum.trans_eq (by dsimp only [D]; ring)

#print axioms fixed_ring_common_bound
end QuantitativeEulerEndpointPrepared
