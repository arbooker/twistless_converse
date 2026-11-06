module

public import QuantitativeEulerEndpointLocalActionV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane QuantitativeEulerDiamondDecode QuantitativeEulerDensityGenerators
open AsymptoticRegularObservationRows AsymptoticCongruenceStrip
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

variable {N : ℕ} [NeZero N] {excluded : Finset ℕ} {threshold : ℕ}
variable (P : Prepared N excluded threshold) (p : ℕ) (hp : 0<p) (w δ : ℂ)

theorem wide_local_control_of_energy (A : Ring)
    (hA : ∀ (q : ℕ) [Fact q.Prime] (hqN : ¬q∣N) {s : Set ℍ} (hs : IsCompact s)
      {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (v : Space),
      ‖compactAction hs hε t x A v‖^2≤localOriginalEnergy p hp w δ q hqN hs hε t x v)
    (g : G) :
    ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧ WideLocalControl P p hp w δ (A*symbol g) B K := by
  obtain ⟨B,hB,K,hK,hbound⟩ := fixed_ring_wide_fresh_bound (symbol g)
  refine ⟨B,hB,K^2,sq_nonneg _,?_⟩
  intro C hBC q hqPrime hqGood
  obtain ⟨_hex,hqN,_ht,_a,_hqa,_hcert⟩ := P.prime_data q Fact.out hqGood
  refine ⟨hqN,?_⟩
  intro s hs ε R Y H hε hY hre hlo him t x v
  let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
  have hCL : C≤L := fresh_transport_height_dominates P C (zero_le_one.trans (hB.trans hBC)) q (Fact.out : q.Prime).one_le
  have hb := hbound L ((hBC).trans hCL) A hs hε hY hre hlo him t x v
  have hb2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  calc
    _ ≤ (K*(wideDistortion L R H)^t*
        ‖compactAction (wideFreshRegion_compact L R H hY) hε t x A v‖)^2 := hb2
    _ = (K^2*((wideDistortion L R H)^t)^2)*
        ‖compactAction (wideFreshRegion_compact L R H hY) hε t x A v‖^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hA q hqN _ hε t x v)
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- Every translated original local row has a common-shape wide bound.
Only the already proved Gamma0 recovery uses the fresh prime. -/
theorem wide_local_translated_control (hw : w*w=1) (i : LocalRowIndex N × G) :
    ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      WideLocalControl P p hp w δ (localTranslatedRow N p (NeZero.pos N) hp w δ i) B K := by
  rcases i with ⟨i,g⟩
  cases i with
  | inl γ =>
    obtain ⟨B,hB,K,hK,hbound⟩ := wide_gamma0_original_control P
      (AsymptoticCongruenceStrip.representative γ) (representative_mem γ) g
    refine ⟨B,hB,K,hK,?_⟩
    intro C hBC q hqPrime hqGood
    obtain ⟨hqN,hqbound⟩ := hbound C hBC q hqGood
    refine ⟨hqN,?_⟩
    intro s hs ε R Y H hε hY hre hlo him t x v
    have hb := hqbound w hw hs hε hY hre hlo him t x v
    rw [representative_label] at hb
    apply hb.trans
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg _))
      (mul_nonneg hK (sq_nonneg _))
  | inr i =>
    apply wide_local_control_of_energy P p hp w δ _ ?_ g
    intro q _ hqN s hs ε hε t x v
    fin_cases i
    · change ‖compactAction hs hε t x (frickeRow N (NeZero.pos N) w) v‖^2≤_
      rw [frickeRow,compactAction_untwisted]
      unfold localOriginalEnergy
      nlinarith [sq_nonneg (‖fixedPrimeStack N w hs hε t x v‖),
        sq_nonneg (‖AsymptoticObservationStack.stack (fun j =>
          AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w hs hε t j x) v‖),
        sq_nonneg (‖bad p hp δ hs hε t x v‖)]
    · change ‖compactAction hs hε t x (ramifiedRow p hp δ) v‖^2≤_
      rw [compactAction_ramified]
      unfold localOriginalEnergy
      exact le_add_of_nonneg_left (by positivity)

#print axioms wide_local_control_of_energy
#print axioms wide_local_translated_control
end QuantitativeEulerEndpointPrepared
