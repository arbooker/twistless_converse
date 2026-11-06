module

public import AsymptoticCongruenceDefectV1
public import AsymptoticRankMonotonicityV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticCongruenceDefect

open UpperHalfPlane Matrix MeasureTheory ContinuousLinearMap
open AsymptoticRegularTrace AsymptoticCornerKernel AsymptoticPolarIsometry
open AsymptoticSubgroupSupport AsymptoticIntegralSubgroup AsymptoticObservationStack
open AsymptoticRegularCompactBranch (Space)
open scoped MatrixGroups ENNReal

/-- A fresh prime in the generator's residue class removes at least
1/(q-1) times the rank of any fixed compact observation of that generator.
The observations and the next kernel are the original weighted equations. -/
theorem rank_loss (N q : ℕ) [Fact q.Prime] (hN : 0<N) (hq : ¬q∣N)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 N) (hd : γ 1 0∣(q:ℤ)-γ 0 0)
    (w : ℂ) (K : CompactExhaustion ℍ) {ε : ℝ} (hε : 0<ε) (t : ℕ)
    (U : ℍ → Submodule ℂ Space) [∀ x,CompleteSpace (U x)]
    (hm : ∀ g h,Measurable (fun x => matrix (U x).starProjection g h))
    (hc : Covariant (fun x => (U x).starProjection))
    (hi : ∀ x,Supported (integralGroup q) (U x).starProjection)
    (hf : trace volume (fun x => (U x).starProjection)<∞)
    (hW : ∀ x v,v∈U x → ∀ s : Set ℍ,∀ hs : IsCompact s,
      AsymptoticRegularObservationRows.twist N 1 hN Nat.zero_lt_one w hs hε t x v=0)
    {s : Set ℍ} (hs : IsCompact s) :
    (trace volume (fun x => ((operator γ hs hε t x).comp (U x).starProjection).kerᗮ.starProjection)).toReal/
        (q-1:ℕ)≤
      (trace volume (fun x => (U x).starProjection)).toReal-
        (trace volume (fun x => (globalRemaining (U x) (fun j =>
          (AsymptoticRegularObservationRows.twist N q hN (Fact.out : q.Prime).pos w
            (K.isCompact j) hε t x).comp (U x).starProjection)).starProjection)).toReal := by
  let T := operator γ hs hε t
  let R := fun x => (U x).starProjection
  let I := fun x => globalRemaining (U x) (fun j => stack
    (AsymptoticFreshRank.observed N q hN hq w (K.isCompact j) hε t R x))
  have hreg := operator_regular γ hs hε t
  have hr := support_matrix_measurable (fun x => (T x).comp (R x))
    (matrix_comp_measurable _ _ hreg.1 hm) (covariant_comp _ _ hreg.2 hc)
    (bound γ hs hε t) (fun x =>
      (restricted_norm_le (U x) (T x)).trans (operator_norm_le γ hs hε t x)) 1 1
  have he := corner_removed_trace volume U (fun x => (T x).comp (R x))
    (fun x => restricted_comp_projection (U x) (T x)) hr hf
  simp only [R,remaining_restricted] at he
  have hinc (x : ℍ) : I x≤remaining (U x) (T x) :=
    global_individual_le_remaining N q hN hq γ hγ hd w K hε t x (U x) (hW x) hs
  have htf := projection_trace_finite_of_le volume (fun x => remaining (U x) (T x)) U
    (fun _ => inf_le_left) hf
  have hmono := ENNReal.toReal_mono htf.ne
    (projection_trace_mono volume I (fun x => remaining (U x) (T x)) hinc)
  have hnum : (trace volume (fun x => ((T x).comp (R x)).kerᗮ.starProjection)).toReal≤
      (trace volume R).toReal-(trace volume (fun x => (I x).starProjection)).toReal := by
    dsimp only [R] at *
    linarith
  have hloss := AsymptoticFreshRank.global_rank_loss N q hN hq w K hε t U (hm 1 1)
    R hm hc hi (fun x => (U x).isIdempotentElem_starProjection)
    1 zero_le_one (fun x => (U x).starProjection_norm_le) hf
  exact (div_le_div_of_nonneg_right hnum (Nat.cast_nonneg (q-1))).trans hloss

#print axioms rank_loss

end AsymptoticCongruenceDefect
