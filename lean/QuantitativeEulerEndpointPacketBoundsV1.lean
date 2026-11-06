module

public import QuantitativeEulerEndpointPacketChainV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory ContinuousLinearMap AsymptoticRegularTrace
open AsymptoticRegularObservationRows AsymptoticRegularBranchFamily
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

theorem primeRescaling_le (q : ℕ) [Fact q.Prime] : primeRescaling q≤2*(q : ℝ) := by
  have hq : 1<(q : ℝ) := by exact_mod_cast (Fact.out : q.Prime).one_lt
  have he := primeRescaling_sq q
  rw [Nat.cast_sub (Fact.out : q.Prime).one_lt.le,Nat.cast_one] at he
  have hp := (primeRescaling_pos q).le
  nlinarith only [he,hp,hq]

variable (N q : ℕ) [Fact q.Prime] (hN : 0<N) (w : ℂ)
variable {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ)

def packetTwistBound : ℝ := 2*(q : ℝ)*
  familyBound (twistBranches N q hN (Fact.out : q.Prime).pos)
    (Sum.elim (fun _ => 1) (fun _ => -w)) hs hε t

theorem normalized_twist_row_norm (x : ℍ) :
    ‖normalizedTwistRow N q hN w hs hε t x‖≤‖twist N q hN (Fact.out : q.Prime).pos w hs hε t x‖ := by
  have hqm : (1 : ℝ)≤((q-1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt (Fact.out : q.Prime).one_lt
  have hr : 1≤Real.sqrt ((q-1 : ℕ) : ℝ) := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hqm
  have hi := (inv_le_one₀ (zero_lt_one.trans_le hr)).mpr hr
  rw [normalizedTwistRow,norm_smul,norm_neg,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0≤(Real.sqrt ((q-1 : ℕ) : ℝ))⁻¹)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hi
    (norm_nonneg (twist N q hN (Fact.out : q.Prime).pos w hs hε t x))

theorem packet_twist_row_norm (x : ℍ) :
    ‖packetTwistRow N q hN w hs hε t x‖≤packetTwistBound N q hN w hs hε t := by
  rw [packetTwistRow,norm_smul,Real.norm_eq_abs,abs_of_nonneg (primeRescaling_pos q).le]
  exact mul_le_mul (primeRescaling_le q)
    ((normalized_twist_row_norm N q hN w hs hε t x).trans (family_norm_le _ _ hs hε t x))
    (norm_nonneg _) (by positivity)

theorem packet_twist_row_regular :
    (∀ g h,Measurable (fun x => matrix (packetTwistRow N q hN w hs hε t x) g h)) ∧
      Covariant (packetTwistRow N q hN w hs hε t) := by
  simp only [packetTwistRow,normalizedTwistRow]
  exact ⟨matrix_smul_measurable _ _ (matrix_smul_measurable _ _ (family_matrix_measurable _ _ hs hε t)),
    covariant_smul _ _ (covariant_smul _ _ (family_covariant _ _ hs hε t))⟩

#print axioms primeRescaling_le
#print axioms packet_twist_row_norm
#print axioms packet_twist_row_regular
end QuantitativeEulerEndpointPrepared
