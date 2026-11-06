module

public import AsymptoticPrimePrefixRowsV1
public import AsymptoticPrimeSequenceV1
public import AsymptoticPersistentRankV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticRegularObservation

open UpperHalfPlane Matrix MeasureTheory ContinuousLinearMap Filter
open AsymptoticRegularTrace AsymptoticRegularObservationRows AsymptoticSectorSigns
open AsymptoticIntegralSubgroup AsymptoticFreshCRT AsymptoticPrimesInAP
open AsymptoticCompactObservationCount (Row)
open AsymptoticRegularCompactBranch (Space)
open FinitenessCertificate FinitenessGlobalHeight
open scoped MatrixGroups ENNReal Topology

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- Every fixed compact congruence defect vanishes on the full kernel
of the original equations. The prime sequence, its reciprocal divergence,
freshness, and the per-stage loss estimates are all derived here. -/
theorem ae_compact_congruence_of_nontriangular (hN : 0<N) (P : Parameters A)
    (r : ℕ → Row N) (hcover : ∀ q : ℕ,∀ hq : 0<q,∃ j,r j=.twist q hq)
    (K : CompactExhaustion ℍ) (e : Sector N)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 N) (h10 : γ 1 0≠0)
    {s : Set ℍ} (hs : IsCompact s) :
    let P' := AsymptoticReconstructedCount.parameters A P
    ∀ᵐ x ∂volume,∀ v∈globalKernelSpace A hN P r K e x,
      AsymptoticCongruenceDefect.operator γ hs P'.epsilon_pos (P'.s+4) x v=0 := by
  let m := (γ 1 0).natAbs
  let : NeZero m := ⟨Int.natAbs_ne_zero.mpr h10⟩
  have hu : IsUnit (γ 0 0:ZMod m) := topLeft_isUnit γ m Int.natAbs_dvd_self
  obtain ⟨q,_,hq,hprev,hdiv⟩ := exists_fresh_prime_sequence hu (N*Q) (Nat.mul_pos hN hQ)
  let hprime : ∀ n,(q n).Prime := fun n => (hq n).1
  have hqN (n : ℕ) : ¬q n∣N := fun h => (hq n).2.1 (dvd_mul_of_dvd_left h Q)
  have hqQ (n : ℕ) : ¬q n∣Q := fun h => (hq n).2.1 (dvd_mul_of_dvd_right h N)
  have hd (n : ℕ) : γ 1 0∣(q n:ℤ)-γ 0 0 := by
    apply Int.natAbs_dvd.mp
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp only [Int.cast_sub,Int.cast_natCast,(hq n).2.2,sub_self]
  let R := primeRows N q hprime
  let P' := AsymptoticReconstructedCount.parameters A P
  let U := globalKernelSpace A hN P r K e
  let V := fun n => prefixKernelSpace A hN P R K e n
  let T := AsymptoticCongruenceDefect.operator γ hs P'.epsilon_pos (P'.s+4)
  have hUV (n : ℕ) (x : ℍ) : U x≤V n x :=
    (globalKernelSpace_le_of_range A hN P R r (primeRows_range_subset r hcover q hprime) K e x).trans
      (globalKernelSpace_le_prefix A hN P R K e n x)
  have hV0 (n : ℕ) (x : ℍ) : V n x≤V 0 x :=
    prefixKernelSpace_antitone A hN P R K e x (Nat.zero_le n)
  have hmV (n : ℕ) := globalKernelProjection_matrix_measurable A hN P (prefixRows R n) K e
  have hcV (n : ℕ) := globalKernelProjection_covariant A hN P (prefixRows R n) K e
  have hmU := globalKernelProjection_matrix_measurable A hN P r K e
  have hcU := globalKernelProjection_covariant A hN P r K e
  have hT := AsymptoticCongruenceDefect.operator_regular γ hs P'.epsilon_pos (P'.s+4)
  have hfin := globalKernelProjection_trace_finite A hN P (prefixRows R 0) K e
  have ha (n : ℕ) : 0≤1/((q n:ℝ)-1) := by
    have hpos : (1:ℝ)<q n := by exact_mod_cast (hprime n).one_lt
    positivity
  have hstep (n : ℕ) :
      (trace volume (fun x => ((T x).comp (V n x).starProjection).kerᗮ.starProjection)).toReal*
        (1/((q n:ℝ)-1))≤
      (trace volume (fun x => (V n x).starProjection)).toReal-
        (trace volume (fun x => (V (n+1) x).starProjection)).toReal := by
    let : Fact (q n).Prime := ⟨hprime n⟩
    have he := prefix_congruence_loss A (q n) hN (hqN n) (hqQ n) P R K e n rfl rfl
      (primeRows_fresh N q hprime hprev n) γ hγ (hd n) hs
    simpa only [Nat.cast_sub (hprime n).one_lt.le,Nat.cast_one,div_eq_mul_inv,one_mul] using he
  exact ae_annihilates_of_divergent_losses volume AsymptoticRationalGroup.measurePreserving V U
    hUV hV0 hmV hmU hcV hcU T hT.1 hT.2
    (AsymptoticCongruenceDefect.bound γ hs P'.epsilon_pos (P'.s+4))
    (fun x => AsymptoticCongruenceDefect.operator_norm_le γ hs P'.epsilon_pos (P'.s+4) x)
    hfin (fun n => 1/((q n:ℝ)-1)) ha hdiv hstep

#print axioms ae_compact_congruence_of_nontriangular

end AsymptoticRegularObservation
