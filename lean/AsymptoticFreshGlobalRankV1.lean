module

public import AsymptoticCompactRestrictionV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticFreshRank

open AsymptoticIntegralSubgroup AsymptoticSubgroupSupport AsymptoticRegularTrace
open AsymptoticRegularCompactBranch (Space)
open AsymptoticRegularObservationRows AsymptoticObservationStack AsymptoticCornerKernel
open AsymptoticMixing UpperHalfPlane MeasureTheory ContinuousLinearMap
open scoped ENNReal

variable (N q : ℕ) [Fact q.Prime] (hN : 0<N) (hq : ¬q∣N)
variable (w : ℂ) (K : CompactExhaustion ℍ) {ε : ℝ} (hε : 0<ε) (t : ℕ)

/-- The one-prime inequality for the intersections of all compact
observations. Compact compatibility discharges the decreasing-kernel
hypotheses required by finite-trace normality. -/
theorem global_rank_loss (P : ℍ → Submodule ℂ Space) [∀ x,CompleteSpace (P x)]
    (hp : Measurable (fun x => matrix (P x).starProjection 1 1))
    (R : ℍ → Space →L[ℂ] Space)
    (hm : ∀ g h,Measurable (fun x => matrix (R x) g h)) (hc : Covariant R)
    (hi : ∀ x,Supported (integralGroup q) (R x))
    (hr : ∀ x,(R x).comp (P x).starProjection=R x)
    (C : ℝ) (hC : 0≤C) (hR : ∀ x,‖R x‖≤C)
    (hf : trace volume (fun x => (P x).starProjection)<∞) :
    ((trace volume (fun x => (P x).starProjection)).toReal-
      (trace volume (fun x => (globalRemaining (P x) (fun n =>
        stack (observed N q hN hq w (K.isCompact n) hε t R x))).starProjection)).toReal)/
      (q-1:ℕ)≤
    (trace volume (fun x => (P x).starProjection)).toReal-
      (trace volume (fun x => (globalRemaining (P x) (fun n =>
        (twist N q hN (Fact.out : q.Prime).pos w (K.isCompact n) hε t x).comp (R x))).starProjection)).toReal := by
  let L := fun n x => observed N q hN hq w (K.isCompact n) hε t R x
  have hreg n := observed_regular N q hN hq w (K.isCompact n) hε t R hm hc
  have hP (n : ℕ) (x : ℍ) (i : Fin (q-1)) : (L n x i).comp (P x).starProjection=L n x i := by
    simp only [L,observed,comp_assoc,hr]
  have hsa (x : ℍ) : Antitone (fun n => remaining (P x) (stack (L n x))) := by
    intro n m hnm
    exact inf_le_inf_left _ (individual_ker_le N q hN hq w
      (K.isCompact n) (K.isCompact m) (K.subset hnm) hε t (R x) x)
  have hba (x : ℍ) : Antitone (fun n => remaining (P x) (mixed (primeLabels q) (L n x))) := by
    intro n m hnm
    dsimp only [L,remaining]
    rw [observed_mixed_ker,observed_mixed_ker]
    exact inf_le_inf_left _ (twist_ker_le N q hN w
      (K.isCompact n) (K.isCompact m) (K.subset hnm) hε t (R x) x)
  have hcard : 0<Fintype.card (Fin (q-1)) := by
    rw [Fintype.card_fin]
    exact Nat.sub_pos_of_lt (Fact.out : q.Prime).one_lt
  have he := AsymptoticMixing.global_rank_loss volume AsymptoticRationalGroup.measurePreserving
    (integralGroup q) (primeLabels q) (primeLabels_separated q) hcard P hp L
    (fun n i => (hreg n i).1) (fun n i => (hreg n i).2)
    (fun n => observed_supported N q hN hq w (K.isCompact n) hε t R hi) hP
    (fun n => stackBound N q hN hq w (K.isCompact n) hε t C)
    (fun n => observed_stack_norm N q hN hq w (K.isCompact n) hε t R C hC hR) hsa hba hf
  simpa only [Fintype.card_fin,L,globalRemaining,remaining,observed_mixed_ker] using he

omit hq in
/-- Exhaustion kernels are independent of the exhaustion: they impose
the existing prime equation on every compact observation region. -/
theorem global_twist_mem_iff (P : Submodule ℂ Space) (R : Space →L[ℂ] Space) (x : ℍ) (f : Space) :
    f∈globalRemaining P (fun n =>
      (twist N q hN (Fact.out : q.Prime).pos w (K.isCompact n) hε t x).comp R) ↔
    f∈P ∧ ∀ s : Set ℍ,∀ hs : IsCompact s,
      twist N q hN (Fact.out : q.Prime).pos w hs hε t x (R f)=0 := by
  simp only [globalRemaining,Submodule.mem_iInf,remaining]
  constructor
  · intro h
    refine ⟨(h 0).1,?_⟩
    intro s hs
    obtain ⟨n,hn⟩ := K.exists_superset_of_isCompact hs
    exact twist_ker_le N q hN w hs (K.isCompact n) hn hε t R x (h n).2
  · intro h n
    exact ⟨h.1,h.2 (K n) (K.isCompact n)⟩

theorem global_individual_mem_iff (P : Submodule ℂ Space) (R : Space →L[ℂ] Space) (x : ℍ) (f : Space) :
    f∈globalRemaining P (fun n =>
      stack (observed N q hN hq w (K.isCompact n) hε t (fun _ => R) x)) ↔
    f∈P ∧ ∀ s : Set ℍ,∀ hs : IsCompact s,∀ i : Fin (q-1),
      AsymptoticFreshCompactDefects.row N q hN hq w hs hε t i x (R f)=0 := by
  simp only [globalRemaining,Submodule.mem_iInf,remaining]
  constructor
  · intro h
    refine ⟨(h 0).1,?_⟩
    intro s hs
    obtain ⟨n,hn⟩ := K.exists_superset_of_isCompact hs
    exact (stack_eq_zero_iff _ f).mp
      (individual_ker_le N q hN hq w hs (K.isCompact n) hn hε t R x (h n).2)
  · intro h n
    exact ⟨h.1,(stack_eq_zero_iff _ f).mpr (h.2 (K n) (K.isCompact n))⟩

#print axioms global_rank_loss
#print axioms global_twist_mem_iff
#print axioms global_individual_mem_iff

end AsymptoticFreshRank
