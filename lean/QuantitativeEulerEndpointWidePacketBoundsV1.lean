module

public import QuantitativeEulerEndpointWideOperatorV1
public import QuantitativeEulerEndpointPacketRegularV1
public import QuantitativeHolomorphicObservationRowBoundsV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory ContinuousLinearMap AsymptoticRegularTrace
open AsymptoticRegularObservationRows AsymptoticRegularBranchFamily
open AsymptoticCertificateBranches QuantitativeHolomorphic
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

/-- A fully explicit norm bound for one original packet row. -/
def widePacketBound (N q : ℕ) (w : ℂ) (R Y H : ℝ) (t : ℕ) : ℝ :=
  4*(q:ℝ)^2*(1+‖w‖)*
    ((2*(wideCompactCutoff (N*q^3:ℕ) R Y H:ℝ)+1)*(wideDistortion (N*q^3:ℕ) R H)^t)

theorem residue_card_le (q : ℕ) : Fintype.card (residues q)≤q := by
  rw [Fintype.card_coe]
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range q)

theorem twist_coefficient_mass (q : ℕ) (w : ℂ) :
    (∑ i : residues q ⊕ residues q, ‖(Sum.elim (fun _ => (1:ℂ)) (fun _ => -w)) i‖)≤
      2*(q:ℝ)*(1+‖w‖) := by
  have hc (i : residues q ⊕ residues q) :
      ‖(Sum.elim (fun _ => (1:ℂ)) (fun _ => -w)) i‖≤1+‖w‖ := by
    cases i <;> simp only [Sum.elim_inl,Sum.elim_inr,norm_one,norm_neg] <;> linarith [norm_nonneg w]
  have hcard : (Fintype.card (residues q ⊕ residues q):ℝ)≤2*(q:ℝ) := by
    rw [Fintype.card_sum,Nat.cast_add]
    have h : (Fintype.card (residues q):ℝ)≤q := by exact_mod_cast residue_card_le q
    linarith
  calc
    _ ≤ ∑ _i : residues q ⊕ residues q, (1+‖w‖) := Finset.sum_le_sum (fun i _ => hc i)
    _ = (Fintype.card (residues q ⊕ residues q):ℝ)*(1+‖w‖) := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)

theorem packet_twist_wide_norm (N q : ℕ) [Fact q.Prime] (hN : 0<N) (w : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε R Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
    (hre : ∀ z∈s, |z.re|≤R) (hlo : ∀ z∈s, Y≤z.im) (hhi : ∀ z∈s, z.im≤H)
    (t : ℕ) (x : ℍ) : ‖packetTwistRow N q hN w hs hε t x‖≤widePacketBound N q w R Y H t := by
  let hq := (Fact.out : q.Prime).pos
  choose M hM hB using twistBranches_integer_representatives N q hN hq
  let W := (2*(wideCompactCutoff (N*q^3:ℕ) R Y H:ℝ)+1)*(wideDistortion (N*q^3:ℕ) R H)^t
  have hW : 0≤W := mul_nonneg (by positivity) (pow_nonneg (wideDistortion_pos _ _ _).le _)
  have hf := family_wide_norm (twistBranches N q hN hq)
    (Sum.elim (fun _ => (1:ℂ)) (fun _ => -w)) hs M hM
    (show (0:ℝ)≤(N*q^3:ℕ) by positivity) hB hY hε hre hlo hhi t x
  have hrow : ‖packetTwistRow N q hN w hs hε t x‖≤2*(q:ℝ)*‖twist N q hN hq w hs hε t x‖ := by
    rw [packetTwistRow,norm_smul,Real.norm_eq_abs,abs_of_nonneg (primeRescaling_pos q).le]
    exact mul_le_mul (primeRescaling_le q) (normalized_twist_row_norm N q hN w hs hε t x)
      (norm_nonneg _) (by positivity)
  have htwist : ‖twist N q hN hq w hs hε t x‖≤(2*(q:ℝ)*(1+‖w‖))*W :=
    hf.trans (mul_le_mul_of_nonneg_right (twist_coefficient_mass q w) hW)
  calc
    _ ≤ 2*(q:ℝ)*((2*(q:ℝ)*(1+‖w‖))*W) :=
      hrow.trans (mul_le_mul_of_nonneg_left htwist (by positivity))
    _ = _ := by unfold widePacketBound; dsimp only [W]; ring

def wideSequenceBound (N : ℕ) (w : ℂ) (R Y H : ℝ) (t : ℕ)
    (l : List (EligiblePrime N)) (i : ℕ) : ℝ :=
  (l.map (fun p => widePacketBound N p.val w R Y H t)).getD i 0

theorem packet_sequence_wide_norm (N : ℕ) (hN : 0<N) (w : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε R Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
    (hre : ∀ z∈s, |z.re|≤R) (hlo : ∀ z∈s, Y≤z.im) (hhi : ∀ z∈s, z.im≤H)
    (t : ℕ) (l : List (EligiblePrime N)) (i : ℕ) (x : ℍ) :
    ‖packetSequence N hN w hs hε t l i x‖≤wideSequenceBound N w R Y H t l i := by
  by_cases hi : i<l.length
  · unfold packetSequence wideSequenceBound
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hi)]
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hi)]
    simp only [List.getElem_map]
    exact packet_twist_wide_norm N l[i].val hN w hs hε hY hre hlo hhi t x
  · unfold packetSequence wideSequenceBound
    rw [List.getD_eq_default _ _ (by simpa only [List.length_map] using Nat.le_of_not_gt hi)]
    rw [List.getD_eq_default _ _ (by simpa only [List.length_map] using Nat.le_of_not_gt hi)]
    simp only [norm_zero,le_refl]

#print axioms twist_coefficient_mass
#print axioms packet_twist_wide_norm
#print axioms packet_sequence_wide_norm
end QuantitativeEulerEndpointPrepared
