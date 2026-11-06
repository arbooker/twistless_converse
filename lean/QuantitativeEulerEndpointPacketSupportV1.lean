module

public import QuantitativeEulerEndpointPacketRegularV1
public import AsymptoticIntegralObservationsV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane AsymptoticSubgroupSupport AsymptoticIntegralSubgroup
open AsymptoticRegularObservationRows
open AsymptoticRegularCompactBranch (Space)

/-- Raw original twist rows retain integrality at every distinct fresh
prime, independently of the observation region and scalar normalization. -/
theorem packetTwistRow_supported (N q r : ℕ) [Fact q.Prime] [Fact r.Prime]
    (hN : 0<N) (hrN : ¬r∣N) (hrq : ¬r∣q) (w : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    Supported (integralGroup r) (packetTwistRow N q hN w hs hε t x) := by
  have hraw : Supported (integralGroup r)
      (twist N q hN (Fact.out : q.Prime).pos w hs hε t x) :=
    compact_family_supported r _ _
      (twistBranches_integral r N q hN (Fact.out : q.Prime).pos hrN hrq) hs hε t x
  have hn : Supported (integralGroup r) (normalizedTwistRow N q hN w hs hε t x) :=
    supported_smul _ _ hraw _
  have he : packetTwistRow N q hN w hs hε t x=
      (primeRescaling q:ℂ) • normalizedTwistRow N q hN w hs hε t x :=
    by
      apply ContinuousLinearMap.ext
      intro v
      exact RCLike.real_smul_eq_coe_smul (K:=ℂ) (primeRescaling q)
        (normalizedTwistRow N q hN w hs hε t x v)
  rw [he]
  exact supported_smul _ _ hn _

theorem packetSequence_supported (N : ℕ) (hN : 0<N) (w : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ)
    (l : List (EligiblePrime N)) (r : EligiblePrime N) (hr : r∉l) (i : ℕ) (x : ℍ) :
    Supported (integralGroup r.val) (packetSequence N hN w hs hε t l i x) := by
  by_cases hi : i<l.length
  · have he : packetSequence N hN w hs hε t l i x=
        packetTwistRow N l[i].val hN w hs hε t x := by
      rw [packetSequence,List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hi),List.getElem_map]
    rw [he]
    apply packetTwistRow_supported N l[i].val r.val hN r.property.2
    apply eligible_not_dvd_of_ne
    intro h
    exact hr (h ▸ List.getElem_mem hi)
  · have he : packetSequence N hN w hs hε t l i x=0 :=
      List.getD_eq_default _ _ (by simpa only [List.length_map] using Nat.le_of_not_gt hi)
    rw [he]
    intro g h _
    rfl

#print axioms packetTwistRow_supported
#print axioms packetSequence_supported
end QuantitativeEulerEndpointPrepared
