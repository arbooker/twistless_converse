module

public import QuantitativeEulerOldProjectionClassicalDimensionBaseV1
public import AsymptoticClassicalMultiplicityRecurrenceV1
public import AsymptoticClassicalNewDimensionPrimesV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeEulerOldProjectionClassicalDimension

open UpperHalfPlane Filter AsymptoticSectorComparison AsymptoticClassicalCusp
open AsymptoticClassicalDimension
open scoped Topology

/-- Finite induction over simply ramified primes propagates an actual base
 bounded dimension error through the proven two-old-image recurrence.
The error constant changes from Bu,Bl to Bu+2Bl at each step. -/
theorem partial_dimension_bounded_difference (b : ℕ) (T : Set ℕ) (C : ℕ → ℝ)
    (hbase : ∀ N (hN : 0 < N), b ∣ N →
      ∃ B : ℝ, ∀ᶠ k : ℕ in evenWeights,
        |(Module.finrank ℂ (partialNewSpace N hN (k : ℤ) T) : ℝ) - C N * k| ≤ B)
    (ps : List ℕ) (N : ℕ) (hN : 0 < N) (hb : b ∣ N)
    (hs : SimplePrimesAt ps N)
    (hc : ∀ p ∈ ps, p.Coprime b)
    (hout : ∀ p ∈ ps, p ∉ T) :
    ∃ B : ℝ, ∀ᶠ k : ℕ in evenWeights,
      |(Module.finrank ℂ (partialNewSpace N hN (k : ℤ) ((ps.toFinset : Set ℕ) ∪ T)) : ℝ) -
        simpleDifference ps C N * k| ≤ B := by
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
    obtain ⟨Bu, hu⟩ := ih (p * M) hN hb hs.tail hc' hout'
    obtain ⟨Bl, hl⟩ := ih M hM hbM hsM hc' hout'
    refine ⟨Bu + 2 * Bl, ?_⟩
    have heven : ∀ᶠ k in evenWeights, Even k :=
      Filter.Eventually.filter_mono inf_le_right
        (Filter.eventually_principal.mpr (fun _ h => h))
    filter_upwards [heven, hu, hl] with k hk hu hl
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
    rw [abs_le] at hu hl ⊢
    constructor <;> nlinarith [hu.1, hu.2, hl.1, hl.2]

#print axioms partial_dimension_bounded_difference

end QuantitativeEulerOldProjectionClassicalDimension
