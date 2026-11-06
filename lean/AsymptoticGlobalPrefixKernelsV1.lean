module

public import AsymptoticGlobalObservationFamiliesV1
public import AsymptoticFreshKernelRankV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticRegularObservation

open UpperHalfPlane MeasureTheory ContinuousLinearMap AsymptoticRegularTrace AsymptoticSectorSigns
open AsymptoticRegularReconstruction AsymptoticRegularObservationRows AsymptoticCornerKernel
open AsymptoticRegularCompactBranch (Space)
open AsymptoticCompactObservationCount (Row)
open FinitenessCertificate FinitenessGlobalHeight AsymptoticIntegralSubgroup AsymptoticSubgroupSupport

def prefixRows {N : ℕ} (r : ℕ → Row N) (n i : ℕ) : Row N := r (min i n)

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- The first n+1 original equations, each imposed on every compact
region. Repeating the last row makes the indexing nonempty even at n=0. -/
noncomputable def prefixKernelSpace (hN : 0<N) (P : Parameters A) (r : ℕ → Row N)
    (K : CompactExhaustion ℍ) (e : Sector N) (n : ℕ) (x : ℍ) : Submodule ℂ Space :=
  globalKernelSpace A hN P (prefixRows r n) K e x

noncomputable instance prefixKernelSpace_complete (hN : 0<N) (P : Parameters A) (r : ℕ → Row N)
    (K : CompactExhaustion ℍ) (e : Sector N) (n : ℕ) (x : ℍ) :
    CompleteSpace (prefixKernelSpace A hN P r K e n x) :=
  inferInstanceAs (CompleteSpace (globalKernelSpace A hN P (prefixRows r n) K e x))

theorem prefixKernelSpace_mem (hN : 0<N) (P : Parameters A) (r : ℕ → Row N)
    (K : CompactExhaustion ℍ) (e : Sector N) (n : ℕ) (x : ℍ) (v : Space) :
    let P' := AsymptoticReconstructedCount.parameters A P
    v∈prefixKernelSpace A hN P r K e n x ↔
      v∈(includedExtension A hN P' (multiplier e) x).range ∧
        ∀ i≤n,∀ s : Set ℍ,∀ hs : IsCompact s,row hN (r i) e hs P'.epsilon_pos (P'.s+4) x v=0 := by
  rw [prefixKernelSpace]
  have he := globalKernelSpace_mem A hN P (prefixRows r n) K e x v
  dsimp only at he
  rw [he]
  apply and_congr_right
  intro _
  constructor
  · intro h i hi
    simpa only [prefixRows,min_eq_left hi] using h i
  · intro h i
    exact h (min i n) (min_le_right i n)

theorem prefixKernelSpace_antitone (hN : 0<N) (P : Parameters A) (r : ℕ → Row N)
    (K : CompactExhaustion ℍ) (e : Sector N) (x : ℍ) :
    Antitone (fun n => prefixKernelSpace A hN P r K e n x) := by
  intro n m hnm v hv
  have hv := (prefixKernelSpace_mem A hN P r K e m x v).mp hv
  exact (prefixKernelSpace_mem A hN P r K e n x v).mpr
    ⟨hv.1,fun i hi => hv.2 i (hi.trans hnm)⟩

theorem globalKernelSpace_le_prefix (hN : 0<N) (P : Parameters A) (r : ℕ → Row N)
    (K : CompactExhaustion ℍ) (e : Sector N) (n : ℕ) (x : ℍ) :
    globalKernelSpace A hN P r K e x≤prefixKernelSpace A hN P r K e n x := by
  intro v hv
  have hv := (globalKernelSpace_mem A hN P r K e x v).mp hv
  exact (prefixKernelSpace_mem A hN P r K e n x v).mpr ⟨hv.1,fun i _ => hv.2 i⟩

theorem globalKernelSpace_eq_iInf_prefix (hN : 0<N) (P : Parameters A) (r : ℕ → Row N)
    (K : CompactExhaustion ℍ) (e : Sector N) (x : ℍ) :
    globalKernelSpace A hN P r K e x=⨅ n,prefixKernelSpace A hN P r K e n x := by
  apply le_antisymm
  · exact le_iInf (fun n => globalKernelSpace_le_prefix A hN P r K e n x)
  · intro v hv
    have hv : ∀ n,v∈prefixKernelSpace A hN P r K e n x := by
      simpa only [Submodule.mem_iInf] using hv
    apply (globalKernelSpace_mem A hN P r K e x v).mpr
    exact ⟨((prefixKernelSpace_mem A hN P r K e 0 x v).mp (hv 0)).1,
      fun i => ((prefixKernelSpace_mem A hN P r K e i x v).mp (hv i)).2 i le_rfl⟩

/-- Adding one complete equation family gives exactly the next prefix
kernel. This equality identifies the trace removed in the one-prime
estimate with the difference of the actual successive kernel traces. -/
theorem prefixKernelSpace_step (hN : 0<N) (P : Parameters A) (r : ℕ → Row N)
    (K : CompactExhaustion ℍ) (e : Sector N) (n : ℕ) (x : ℍ) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let U := prefixKernelSpace A hN P r K e n x
    globalRemaining U (fun j =>
      (row hN (r (n+1)) e (K.isCompact j) P'.epsilon_pos (P'.s+4) x).comp U.starProjection)=
      prefixKernelSpace A hN P r K e (n+1) x := by
  dsimp only
  ext v
  simp only [globalRemaining,remaining,Submodule.mem_iInf,Submodule.mem_inf,LinearMap.mem_ker]
  constructor
  · intro h
    have hv := (h 0).1
    have hprev := (prefixKernelSpace_mem A hN P r K e n x v).mp hv
    have hnew := (exhaustion_zero_iff hN (r (n+1)) e K
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4) x v).mp (fun j => by
        have he := (h j).2
        change row hN (r (n+1)) e (K.isCompact j)
          (AsymptoticReconstructedCount.parameters A P).epsilon_pos
          ((AsymptoticReconstructedCount.parameters A P).s+4) x
          ((prefixKernelSpace A hN P r K e n x).starProjection v)=0 at he
        simpa only [Submodule.starProjection_eq_self_iff.mpr hv] using he)
    apply (prefixKernelSpace_mem A hN P r K e (n+1) x v).mpr
    refine ⟨hprev.1,?_⟩
    intro i hi
    by_cases hn : i≤n
    · exact hprev.2 i hn
    · have he : i=n+1 := by omega
      simpa only [he] using hnew
  · intro hv j
    have hprev := prefixKernelSpace_antitone A hN P r K e x (Nat.le_succ n) hv
    have hnew := ((prefixKernelSpace_mem A hN P r K e (n+1) x v).mp hv).2 (n+1) le_rfl
    refine ⟨hprev,?_⟩
    change row hN (r (n+1)) e (K.isCompact j)
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4) x
      ((prefixKernelSpace A hN P r K e n x).starProjection v)=0
    simpa only [Submodule.starProjection_eq_self_iff.mpr hprev] using hnew (K j) (K.isCompact j)

theorem prefixKernelProjection_supported (q : ℕ) [Fact q.Prime]
    (hN : 0<N) (hqN : ¬q∣N) (hqQ : ¬q∣Q) (P : Parameters A) (r : ℕ → Row N)
    (K : CompactExhaustion ℍ) (e : Sector N) (n : ℕ)
    (hf : ∀ i≤n,Fresh q (r i)) (x : ℍ) :
    Supported (integralGroup q) (prefixKernelSpace A hN P r K e n x).starProjection :=
  infiniteKernelProjection_supported q A hN hqN hqQ P
    (familyRows (prefixRows r n)) (fun j => hf (min (Nat.unpair j).1 n) (min_le_right _ _))
    (familyRegions K) (familyRegions_compact K) e x

#print axioms prefixKernelSpace_mem
#print axioms prefixKernelSpace_antitone
#print axioms globalKernelSpace_le_prefix
#print axioms globalKernelSpace_eq_iInf_prefix
#print axioms prefixKernelSpace_step
#print axioms prefixKernelProjection_supported

end AsymptoticRegularObservation
