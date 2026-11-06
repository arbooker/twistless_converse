module

public import QuantitativeEulerEndpointCanonicalRecoveryV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane QuantitativeArithmetic QuantitativeHolomorphic
open QuantitativeEulerDensityGenerators QuantitativeEulerDiamondDecode
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

theorem fresh_transport_height_dominates {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (C : ℝ) (hC : 0≤C) (q : ℕ) (hq : 1≤q) :
    C≤(2*generatorTransportConstant P*C)*(q : ℝ)^4 := by
  have hs := Finset.sum_nonneg (fun a (_ : a∈(Finset.univ : Finset (UnitResidue N))) =>
    Finset.sum_nonneg (fun i (_ : i∈(Finset.univ : Finset (Option (Generator N)))) =>
      (localTransportConstant_pos P a i).le))
  have ht : 1≤transportConstant P := by unfold transportConstant; linarith
  have hg := generatorHeight_one_le N
  have hc : 1≤2*generatorTransportConstant P := by
    have hp := mul_le_mul ht hg (by norm_num : (0 : ℝ)≤1) (zero_le_one.trans ht)
    unfold generatorTransportConstant
    nlinarith
  have hq' : (1 : ℝ)≤q := by exact_mod_cast hq
  have hq4 : (1 : ℝ)≤(q : ℝ)^4 := one_le_pow₀ hq'
  have h1 := mul_le_mul_of_nonneg_right hc hC
  have h2 := mul_le_mul_of_nonneg_left hq4
    (mul_nonneg (zero_le_one.trans hc) hC)
  simp only [one_mul,mul_one] at h1 h2
  exact h1.trans h2

theorem fixed_ring_fresh_bound (E : Ring) :
    ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ (C : ℝ), B≤C → ∀ (A : Ring) {s : Set ℍ} (hs : IsCompact s)
        {ε Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
        (_hre : ∀ z∈s, |z.re|≤1) (_hlo : ∀ z∈s, Y≤z.im) (_him : ∀ z∈s, z.im≤H)
        (t : ℕ) (x : ℍ) (v : Space),
      ‖compactAction hs hε t x (A*E) v‖≤
        K*(integerCompactDistortion C H)^t*
          ‖compactAction (freshObservationRegion_compact C H hY) hε t x A v‖ := by
  obtain ⟨B,hB,K,hK,hbound⟩ := fixed_ring_common_bound E
  refine ⟨B,hB,K,hK,?_⟩
  intro C hBC A s hs ε Y H hε hY hre hlo him t x v
  have ht := hbound C hBC A hs hε hY hre hlo him t x v
  have hr := compactAction_restrict_norm A (commonImageRegion_compact C H hY)
    (freshObservationRegion_compact C H hY) (common_subset_fresh C Y H) hε t x v
  exact ht.trans (mul_le_mul_of_nonneg_left hr
    (mul_nonneg hK (by unfold integerCompactDistortion; positivity)))

theorem three_vector_squared (u v z : Space) :
    ‖u+v-z‖^2≤3*(‖u‖^2+‖v‖^2+‖z‖^2) := by
  have h := (norm_sub_le (u+v) z).trans
    (add_le_add (norm_add_le u v) (le_refl _))
  have h2 := (sq_le_sq₀ (norm_nonneg _)
    (add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _))).2 h
  nlinarith [sq_nonneg (‖u‖-‖v‖),sq_nonneg (‖u‖-‖z‖),sq_nonneg (‖v‖-‖z‖)]

#print axioms fresh_transport_height_dominates
#print axioms fixed_ring_fresh_bound
#print axioms three_vector_squared
end QuantitativeEulerEndpointPrepared
