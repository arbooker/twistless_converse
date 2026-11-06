module

public import AsymptoticClassicalMultiplicityRecurrenceV1
public import AsymptoticClassicalNewDimensionPrimesV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalDimension

open UpperHalfPlane Filter Asymptotics AsymptoticSectorComparison AsymptoticClassicalCusp
open scoped Topology

/-- Finite induction over simply ramified primes propagates an actual base
 dimension estimate through the proven two-old-image recurrence. -/
theorem partial_dimension_difference (b : ℕ) (T : Set ℕ) (C : ℕ → ℝ)
    (hbase : ∀ N (hN : 0 < N), b ∣ N →
      (fun k : ℕ => (Module.finrank ℂ (partialNewSpace N hN (k : ℤ) T) : ℝ) - C N * k)
        =o[evenWeights] (fun k => (k : ℝ)))
    (ps : List ℕ) (N : ℕ) (hN : 0 < N) (hb : b ∣ N)
    (hs : SimplePrimesAt ps N)
    (hc : ∀ p ∈ ps, p.Coprime b)
    (hout : ∀ p ∈ ps, p ∉ T) :
    (fun k : ℕ =>
      (Module.finrank ℂ (partialNewSpace N hN (k : ℤ) ((ps.toFinset : Set ℕ) ∪ T)) : ℝ) -
        simpleDifference ps C N * k) =o[evenWeights] (fun k => (k : ℝ)) := by
  induction ps generalizing N with
  | nil =>
    have hset : (([].toFinset : Finset ℕ) : Set ℕ) ∪ T = T := by ext p; simp
    have hdim (k : ℕ) := congrArg
      (fun U : Set ℕ => Module.finrank ℂ (partialNewSpace N hN (k : ℤ) U)) hset
    simpa only [hdim, simpleDifference] using hbase N hN hb
  | cons p ps ih =>
    have hp := hs.2 p List.mem_cons_self
    obtain ⟨M, rfl⟩ := hp.2.1
    have hM : 0 < M := by nlinarith
    let : NeZero M := ⟨hM.ne'⟩
    let : NeZero p := ⟨hp.1.ne_zero⟩
    have hd : p * M / p = M := Nat.mul_div_cancel_left M hp.1.pos
    have hsM : SimplePrimesAt ps M := by simpa only [hd] using hs.tail_div hN
    have hbM : b ∣ M := by
      simpa only [hd] using base_dvd_div hb (Nat.dvd_mul_right p M) (hc p List.mem_cons_self)
    have hc' : ∀ q ∈ ps, q.Coprime b := fun q hq => hc q (List.mem_cons_of_mem p hq)
    have hout' : ∀ q ∈ ps, q ∉ T := fun q hq => hout q (List.mem_cons_of_mem p hq)
    have hu := ih (p * M) hN hb hs.tail hc' hout'
    have hl := ih M hM hbM hsM hc' hout'
    apply (hu.sub (hl.const_mul_left 2)).congr' ?_ Filter.EventuallyEq.rfl
    have heven : ∀ᶠ k in evenWeights, Even k :=
      Filter.Eventually.filter_mono inf_le_right
        (Filter.eventually_principal.mpr (fun _ h => h))
    filter_upwards [heven] with k hk
    have hpS : p ∉ (ps.toFinset : Set ℕ) ∪ T := by
      simp only [Set.mem_union, Finset.mem_coe, List.mem_toFinset, not_or]
      exact ⟨(List.nodup_cons.mp hs.1).1, hout p List.mem_cons_self⟩
    have hcop : p.Coprime M := by simpa only [hd] using hp.2.2
    have he := partialNewSpace_simple_finrank M p hM hp.1 hcop k hk
      ((ps.toFinset : Set ℕ) ∪ T) hpS
    have heR :
        (Module.finrank ℂ (partialNewSpace (p * M) hN (k : ℤ)
          (insert p ((ps.toFinset : Set ℕ) ∪ T))) : ℝ) +
        2 * (Module.finrank ℂ (partialNewSpace M hM (k : ℤ)
          ((ps.toFinset : Set ℕ) ∪ T)) : ℝ) =
        (Module.finrank ℂ (partialNewSpace (p * M) hN (k : ℤ)
          ((ps.toFinset : Set ℕ) ∪ T)) : ℝ) := by exact_mod_cast he
    have hset : ((p :: ps).toFinset : Set ℕ) ∪ T = insert p ((ps.toFinset : Set ℕ) ∪ T) := by
      ext q
      simp [or_assoc]
    have hdim := congrArg
      (fun U : Set ℕ => Module.finrank ℂ (partialNewSpace (p * M) hN (k : ℤ) U)) hset
    rw [hdim]
    simp only [simpleDifference, hd]
    nlinarith

#print axioms partial_dimension_difference

end AsymptoticClassicalDimension
