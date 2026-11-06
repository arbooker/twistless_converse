module

public import QuantitativeEulerEndpointPacketBoundsV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory AsymptoticRegularTrace
open scoped Classical

variable (N : ℕ) (hN : 0<N) (w : ℂ) {s : Set ℍ} (hs : IsCompact s)
variable {ε : ℝ} (hε : 0<ε) (t : ℕ) (l : List (EligiblePrime N))

def packetSequenceBound (i : ℕ) : ℝ :=
  (l.map (fun p => packetTwistBound N p.val hN w hs hε t)).getD i 0

theorem packet_sequence_regular (i : ℕ) :
    (∀ g h,Measurable (fun x => matrix (packetSequence N hN w hs hε t l i x) g h)) ∧
      Covariant (packetSequence N hN w hs hε t l i) := by
  by_cases hi : i<l.length
  · have he : packetSequence N hN w hs hε t l i=packetTwistRow N l[i].val hN w hs hε t := by
      funext x
      rw [packetSequence,List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hi),List.getElem_map]
    rw [he]
    exact packet_twist_row_regular N l[i].val hN w hs hε t
  · have he : packetSequence N hN w hs hε t l i=fun _ => 0 := by
      funext x
      exact List.getD_eq_default _ _ (by simpa only [List.length_map] using Nat.le_of_not_gt hi)
    rw [he]
    constructor
    · intro g h
      simp only [matrix,_root_.zero_apply,lp.coeFn_zero,Pi.zero_apply]
      exact measurable_const
    · intro x a g h
      rfl

theorem packet_sequence_norm (i : ℕ) (x : ℍ) :
    ‖packetSequence N hN w hs hε t l i x‖≤packetSequenceBound N hN w hs hε t l i := by
  by_cases hi : i<l.length
  · unfold packetSequence packetSequenceBound
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hi)]
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hi)]
    simp only [List.getElem_map]
    exact packet_twist_row_norm N l[i].val hN w hs hε t x
  · unfold packetSequence packetSequenceBound
    rw [List.getD_eq_default _ _ (by simpa only [List.length_map] using Nat.le_of_not_gt hi)]
    rw [List.getD_eq_default _ _ (by simpa only [List.length_map] using Nat.le_of_not_gt hi)]
    simp only [norm_zero,le_refl]

#print axioms packet_sequence_regular
#print axioms packet_sequence_norm
end QuantitativeEulerEndpointPrepared
