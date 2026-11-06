module

public import QuantitativeEulerEndpointRecoveryRightV1
public import QuantitativeEulerEndpointWideTransportV1
public import QuantitativeEulerEndpointWideFreshRegionV1

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
theorem fixed_ring_wide_bound (E : Ring) :
    ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ (C : ℝ), B≤C → ∀ (A : Ring) {s : Set ℍ} (hs : IsCompact s)
        {ε R Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
        (_hre : ∀ z∈s, |z.re|≤R) (_hlo : ∀ z∈s, Y≤z.im) (_him : ∀ z∈s, z.im≤H)
        (t : ℕ) (x : ℍ) (v : Space),
      ‖compactAction hs hε t x (A*E) v‖≤
        K*(wideDistortion C R H)^t*
          ‖compactAction (wideImageRegion_compact C R H hY) hε t x A v‖ := by
  let J := ↥E.coeff.support
  obtain ⟨B,hB,hmat⟩ := QuantitativeEulerIntegerHeight.finite_family_height
    (fun g : J => g.val)
  let K : ℝ := ∑ g : J, ‖E.coeff g.val‖
  refine ⟨B,hB,K,Finset.sum_nonneg (fun g _ => norm_nonneg _),?_⟩
  intro C hBC A s hs ε R Y H hε hY hre hlo him t x v
  have hC : 0≤C := zero_le_one.trans (hB.trans hBC)
  let D := (wideDistortion C R H)^t*
    ‖compactAction (wideImageRegion_compact C R H hY) hε t x A v‖
  have hrow (g : J) : ‖compactAction hs hε t x (A*symbol g.val) v‖≤D := by
    obtain ⟨M,hM,hMb⟩ := hmat g
    exact compact_right_wide_bound g.val hM hC (entry_bound_mono hMb hBC) hY
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

theorem fixed_ring_wide_fresh_bound (E : Ring) :
    ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ (C : ℝ), B≤C → ∀ (A : Ring) {s : Set ℍ} (hs : IsCompact s)
        {ε R Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
        (_hre : ∀ z∈s, |z.re|≤R) (_hlo : ∀ z∈s, Y≤z.im) (_him : ∀ z∈s, z.im≤H)
        (t : ℕ) (x : ℍ) (v : Space),
      ‖compactAction hs hε t x (A*E) v‖≤
        K*(wideDistortion C R H)^t*
          ‖compactAction (wideFreshRegion_compact C R H hY) hε t x A v‖ := by
  obtain ⟨B,hB,K,hK,hbound⟩ := fixed_ring_wide_bound E
  refine ⟨B,hB,K,hK,?_⟩
  intro C hBC A s hs ε R Y H hε hY hre hlo him t x v
  have ht := hbound C hBC A hs hε hY hre hlo him t x v
  have hr := compactAction_restrict_norm A (wideImageRegion_compact C R H hY)
    (wideFreshRegion_compact C R H hY) (wide_subset_fresh C R Y H) hε t x v
  exact ht.trans (mul_le_mul_of_nonneg_left hr
    (mul_nonneg hK (by unfold wideDistortion; positivity)))

#print axioms fixed_ring_wide_bound
#print axioms fixed_ring_wide_fresh_bound
end QuantitativeEulerEndpointPrepared
