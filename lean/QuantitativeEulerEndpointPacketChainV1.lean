module

public import QuantitativeEulerEndpointPacketRowsV1
public import Mathlib.Data.List.GetD

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane ContinuousLinearMap QuantitativeSpectralDeflationChain
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem chain_list_prefix (U : ClosedSubmodule ℂ H) (rows : List (H →L[ℂ] H))
    (c : ℝ) (n : ℕ) (hn : n≤rows.length) :
    chain U (fun i => rows.getD i 0) c n=(rows.take n).foldl (fun V B => step V B c) U := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hlt : n<rows.length := by omega
    rw [chain,ih (by omega),List.take_succ_eq_append_getElem hlt,List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil,List.getD_eq_getElem rows 0 hlt]

theorem chain_list_full (U : ClosedSubmodule ℂ H) (rows : List (H →L[ℂ] H)) (c : ℝ) :
    chain U (fun i => rows.getD i 0) c rows.length=rows.foldl (fun V B => step V B c) U := by
  rw [chain_list_prefix U rows c rows.length le_rfl,List.take_length]
end Hilbert

variable (N : ℕ) (hN : 0<N) (w : ℂ) {s : Set ℍ} (hs : IsCompact s)
variable {ε : ℝ} (hε : 0<ε) (t : ℕ)

theorem primeChain_eq_fold (c : ℝ) (hc : 0<c) (U : ℍ → ClosedSubmodule ℂ Space)
    (l : List (EligiblePrime N)) (x : ℍ) :
    primeChain N hN w hs hε t c U l x=
      l.foldl (fun V p => step V (packetTwistRow N p.val hN w hs hε t x) c) (U x) := by
  induction l generalizing U with
  | nil => rfl
  | cons p l ih =>
    rw [primeChain,List.foldl_cons,ih]
    congr 1
    apply SetLike.coe_injective
    change (freshStepSource N p.val hN p.property.2 w hs hε t
      (fun y => (U y).toSubmodule) (primeCut c p.val) x : Set Space)=
      (QuantitativeSpectralCornerCutRow.nextSpace (U x).toSubmodule
        (packetTwistRow N p.val hN w hs hε t x) c : Set Space)
    rw [freshStep_eq_packet N p.val hN p.property.2 w hs hε t _ c hc x]

/-- A finite sequence of raw original twist rows, extended by zero.
It depends on the prime list, not on intermediate spectral projections. -/
def packetSequence (l : List (EligiblePrime N)) (i : ℕ) (x : ℍ) : Space →L[ℂ] Space :=
  (l.map (fun p => packetTwistRow N p.val hN w hs hε t x)).getD i 0

theorem primeChain_eq_packet (c : ℝ) (hc : 0<c) (U : ℍ → ClosedSubmodule ℂ Space)
    (l : List (EligiblePrime N)) (x : ℍ) :
    primeChain N hN w hs hε t c U l x=
      chain (U x) (fun i => packetSequence N hN w hs hε t l i x) c l.length := by
  rw [primeChain_eq_fold N hN w hs hε t c hc U l x]
  have hh := chain_list_full (U x) (l.map (fun p => packetTwistRow N p.val hN w hs hε t x)) c
  simpa only [List.length_map,List.foldl_map,packetSequence] using hh.symm

#print axioms chain_list_full
#print axioms primeChain_eq_fold
#print axioms primeChain_eq_packet
end QuantitativeEulerEndpointPrepared
