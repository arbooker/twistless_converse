module

public import QuantitativeMaassRawOriginalRowFamilyV1
public import QuantitativeMaassRawReplacementGramExpansionV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass.RawPrepared
open UpperHalfPlane ContinuousLinearMap AsymptoticSectorSigns
open QuantitativeEulerEndpointPrepared AsymptoticCompactObservationCount QuantitativeEulerDensityGenerators
open AsymptoticRegularCompactBranch (Space)
open AsymptoticRegularObservationRows
variable {N : ℕ} [NeZero N] (e : Sector N) {ε : ℝ} (hε : 0<ε) (t : ℕ)
    (x : ℍ) (u : Space)
    (hu : ∀ (r : Row N) (s : Set ℍ) (hs : IsCompact s),row (NeZero.pos N) r e hs hε t x u=0)

include hu in
theorem regular_baseline_zero_of_original_rows {s : Set ℍ} (hs : IsCompact s)
    (i : NewBaselineIndex N) : newBaselineRows N e hs hε t x i u=0 := by
  cases i with
  | inl i =>
    cases i with
    | none =>
      simpa only [newBaselineRows,baselineRows,row,multiplier_one] using
        hu (.twist 1 Nat.zero_lt_one) s hs
    | some a =>
      have hf : ¬(primeLift N a).q∣N := fun hd =>
        (not_le_of_gt (primeLift N a).large) (Nat.le_of_dvd (NeZero.pos N) hd)
      simpa only [newBaselineRows,baselineRows,row,multiplier_fresh e (primeLift N a).prime hf] using
        hu (.twist (primeLift N a).q (primeLift N a).prime.pos) s hs
  | inr p =>
    simpa only [newBaselineRows,row] using hu (.ramified p.val
      (Nat.mem_primeFactors.mp p.property).1 (Nat.mem_primeFactors.mp p.property).2.1) s hs

include hu in
theorem regular_packet_zero_of_original_rows {s : Set ℍ} (hs : IsCompact s)
    (l : List (EligiblePrime N)) (i : Fin l.length) :
    packetSequence N (NeZero.pos N) (sign e.1) hs hε t l i x u=0 := by
  have hz := hu (.twist l[i.val].val l[i.val].property.1.pos) s hs
  rw [row,multiplier_fresh e l[i.val].property.1 l[i.val].property.2] at hz
  unfold packetSequence
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using i.isLt),List.getElem_map,
    packet_twist_row_eq,smul_apply,hz,smul_zero]

#print axioms regular_baseline_zero_of_original_rows
#print axioms regular_packet_zero_of_original_rows
end QuantitativeMaass.RawPrepared
