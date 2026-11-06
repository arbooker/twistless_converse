module

public import QuantitativeEulerEndpointCutScalingV1
public import QuantitativeEulerEndpointPrimeChainV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane ContinuousLinearMap AsymptoticRegularObservationRows
open QuantitativeSpectralCornerCutRow QuantitativeSpectralPacketContraction
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

def primeRescaling (q : ℕ) : ℝ := Real.sqrt (2*(q : ℝ)*((q-1 : ℕ) : ℝ))

theorem primeRescaling_pos (q : ℕ) [Fact q.Prime] : 0<primeRescaling q := by
  have hq : 0<(q : ℝ) := by exact_mod_cast (Fact.out : q.Prime).pos
  have hqm : 0<((q-1 : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt (Fact.out : q.Prime).one_lt
  apply Real.sqrt_pos.mpr
  positivity

theorem primeRescaling_sq (q : ℕ) : (primeRescaling q)^2=2*(q : ℝ)*((q-1 : ℕ) : ℝ) := by
  apply Real.sq_sqrt
  positivity

theorem primeRescaling_cut (c : ℝ) (hc : 0<c) (q : ℕ) [Fact q.Prime] :
    primeRescaling q*primeCut c q=c := by
  have hq : (q : ℝ)≠0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hqm : ((q-1 : ℕ) : ℝ)≠0 := by exact_mod_cast (Nat.sub_pos_of_lt (Fact.out : q.Prime).one_lt).ne'
  apply (sq_eq_sq₀ (mul_nonneg (primeRescaling_pos q).le (primeCut_pos c hc q).le) hc.le).mp
  rw [mul_pow,primeRescaling_sq,primeCut_sq]
  field_simp

/-- A raw original twist, normalized as in the actual mixing identity. -/
def normalizedTwistRow (N q : ℕ) [Fact q.Prime] (hN : 0<N) (w : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) : Space →L[ℂ] Space :=
  -(((Real.sqrt ((q-1 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • twist N q hN (Fact.out : q.Prime).pos w hs hε t x

/-- The prime-dependent normalization moves entirely into the raw row,
leaving the SAME spectral threshold c at every step. -/
def packetTwistRow (N q : ℕ) [Fact q.Prime] (hN : 0<N) (w : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) : Space →L[ℂ] Space :=
  primeRescaling q • normalizedTwistRow N q hN w hs hε t x

theorem freshStep_eq_packet (N q : ℕ) [Fact q.Prime] (hN : 0<N) (hqN : ¬q∣N)
    (w : ℂ) {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ)
    (U : ℍ → Submodule ℂ Space) [∀ x, CompleteSpace (U x)] (c : ℝ) (hc : 0<c) (x : ℍ) :
    freshStepSource N q hN hqN w hs hε t U (primeCut c q) x=
      nextSpace (U x) (packetTwistRow N q hN w hs hε t x) c := by
  rw [fresh_step_source_eq_original]
  have he : normalizedSourceTwist N q hN w hs hε t U x=
      (normalizedTwistRow N q hN w hs hε t x).comp (U x).starProjection := by
    simp only [normalizedSourceTwist,normalizedTwistRow,smul_comp]
  rw [he,nextSpace_restricted]
  have hh := nextSpace_positive_scale (U x) (normalizedTwistRow N q hN w hs hε t x)
    (primeRescaling q) (primeRescaling_pos q) (primeCut c q)
  rw [primeRescaling_cut c hc q] at hh
  exact hh.symm

#print axioms primeRescaling_cut
#print axioms freshStep_eq_packet
end QuantitativeEulerEndpointPrepared
