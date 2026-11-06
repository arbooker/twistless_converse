module

public import AsymptoticGlobalPrefixKernelsV1
public import AsymptoticCongruenceRankLossV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticRegularObservation

open UpperHalfPlane Matrix MeasureTheory ContinuousLinearMap
open AsymptoticRegularTrace AsymptoticRegularObservationRows AsymptoticSectorSigns
open AsymptoticIntegralSubgroup AsymptoticCornerKernel
open AsymptoticCompactObservationCount (Row)
open FinitenessCertificate FinitenessGlobalHeight
open scoped MatrixGroups ENNReal

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- The generator-rank inequality on the literal successive global
prefix kernels. All regularity, support, finite-trace, untwisted-law and
kernel-update hypotheses are discharged by the original observations. -/
theorem prefix_congruence_loss (q : ℕ) [Fact q.Prime]
    (hN : 0<N) (hqN : ¬q∣N) (hqQ : ¬q∣Q) (P : Parameters A)
    (r : ℕ → Row N) (K : CompactExhaustion ℍ) (e : Sector N) (n : ℕ)
    (hzero : r 0=.twist 1 Nat.zero_lt_one)
    (hnext : r (n+1)=.twist q (Fact.out : q.Prime).pos)
    (hfresh : ∀ i≤n,Fresh q (r i))
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 N) (hd : γ 1 0∣(q:ℤ)-γ 0 0)
    {s : Set ℍ} (hs : IsCompact s) :
    let P' := AsymptoticReconstructedCount.parameters A P
    (trace volume (fun x => ((AsymptoticCongruenceDefect.operator γ hs P'.epsilon_pos (P'.s+4) x).comp
      (prefixKernelSpace A hN P r K e n x).starProjection).kerᗮ.starProjection)).toReal/(q-1:ℕ)≤
      (trace volume (fun x => (prefixKernelSpace A hN P r K e n x).starProjection)).toReal-
        (trace volume (fun x => (prefixKernelSpace A hN P r K e (n+1) x).starProjection)).toReal := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let U := prefixKernelSpace A hN P r K e n
  have hm := globalKernelProjection_matrix_measurable A hN P (prefixRows r n) K e
  have hc := globalKernelProjection_covariant A hN P (prefixRows r n) K e
  have hi := prefixKernelProjection_supported A q hN hqN hqQ P r K e n hfresh
  have ht := globalKernelProjection_trace_finite A hN P (prefixRows r n) K e
  have hW (x : ℍ) (v : AsymptoticRegularCompactBranch.Space) (hv : v∈U x)
      (s : Set ℍ) (hs : IsCompact s) :
      twist N 1 hN Nat.zero_lt_one (sign e.1) hs P'.epsilon_pos (P'.s+4) x v=0 := by
    have he := ((prefixKernelSpace_mem A hN P r K e n x v).mp hv).2 0 (Nat.zero_le n) s hs
    simpa only [hzero,AsymptoticRegularObservationRows.row,multiplier_one] using he
  have hloss := AsymptoticCongruenceDefect.rank_loss N q hN hqN γ hγ hd (sign e.1) K
    P'.epsilon_pos (P'.s+4) U hm hc hi ht hW hs
  have hstep (x : ℍ) : globalRemaining (U x) (fun j =>
      (twist N q hN (Fact.out : q.Prime).pos (sign e.1) (K.isCompact j)
        P'.epsilon_pos (P'.s+4) x).comp (U x).starProjection)=
      prefixKernelSpace A hN P r K e (n+1) x := by
    have he := prefixKernelSpace_step A hN P r K e n x
    dsimp only at he
    simpa only [hnext,AsymptoticRegularObservationRows.row,multiplier_fresh e (Fact.out : q.Prime) hqN] using he
  simpa only [hstep] using hloss

#print axioms prefix_congruence_loss

end AsymptoticRegularObservation
