module

public import QuantitativeEulerEndpointPacketBoundsV1
public import QuantitativeSpectralPacketAssemblyV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane ContinuousLinearMap AsymptoticRegularObservationRows
open QuantitativeSpectralDeflationChain QuantitativeSpectralPacketAssembly
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

variable (N q : ℕ) [Fact q.Prime] (hN : 0<N) (w : ℂ)
variable {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ)

theorem packet_twist_row_eq (x : ℍ) :
    packetTwistRow N q hN w hs hε t x=
      (-Real.sqrt (2*(q : ℝ))) • twist N q hN (Fact.out : q.Prime).pos w hs hε t x := by
  have hqm : 0<((q-1 : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt (Fact.out : q.Prime).one_lt
  have he : normalizedTwistRow N q hN w hs hε t x=
      (-(Real.sqrt ((q-1 : ℕ) : ℝ))⁻¹) • twist N q hN (Fact.out : q.Prime).pos w hs hε t x := by
    simp only [normalizedTwistRow,←Complex.ofReal_neg]
    rfl
  rw [packetTwistRow,he,smul_smul]
  have hscalar : primeRescaling q * (-(Real.sqrt ((q-1 : ℕ) : ℝ))⁻¹)= -Real.sqrt (2*(q : ℝ)) := by
    rw [primeRescaling,Real.sqrt_mul (by positivity : (0 : ℝ)≤2*q),mul_neg,mul_assoc,
      mul_inv_cancel₀ (Real.sqrt_pos.mpr hqm).ne',mul_one]
  rw [hscalar]

theorem packet_twist_row_gram (x : ℍ) :
    star (packetTwistRow N q hN w hs hε t x)*packetTwistRow N q hN w hs hε t x=
      (2*(q : ℝ)) • (star (twist N q hN (Fact.out : q.Prime).pos w hs hε t x)*
        twist N q hN (Fact.out : q.Prime).pos w hs hε t x) := by
  rw [packet_twist_row_eq,gram_real_scale,neg_sq,Real.sq_sqrt (by positivity : (0 : ℝ)≤2*q)]

omit [Fact q.Prime] in
/-- The assembled packet Gram is dominated by the actual original-row
Gram sum, with exact scalar weights 2q and no extra number-of-primes factor. -/
theorem actual_packet_gram_le (U : ClosedSubmodule ℂ Space) (c : ℝ) (hc : 0<c)
    (l : List (EligiblePrime N)) (x : ℍ) :
    star (∑ i : Fin l.length, packetRow U (fun j => packetSequence N hN w hs hε t l j x) c i)*
      (∑ i : Fin l.length, packetRow U (fun j => packetSequence N hN w hs hε t l j x) c i)≤
      ∑ i : Fin l.length, (2*(l[i.val].val : ℝ)) •
        (star (twist N l[i.val].val hN l[i.val].property.1.pos w hs hε t x)*
          twist N l[i.val].val hN l[i.val].property.1.pos w hs hε t x) := by
  apply (assembled_gram_le U (fun j => packetSequence N hN w hs hε t l j x) hc l.length).trans_eq
  apply Finset.sum_congr rfl
  intro i hi
  have he : packetSequence N hN w hs hε t l i.val x=
      packetTwistRow N l[i.val].val hN w hs hε t x := by
    unfold packetSequence
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using i.isLt),List.getElem_map]
  rw [he]
  exact packet_twist_row_gram N l[i.val].val hN w hs hε t x

#print axioms packet_twist_row_eq
#print axioms packet_twist_row_gram
#print axioms actual_packet_gram_le
end QuantitativeEulerEndpointPrepared
