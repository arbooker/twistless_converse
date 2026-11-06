module

public import AsymptoticClassicalOldIntersectionRepeatedV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane AsymptoticCongruenceStrip
open scoped ModularForm

/-- Restriction ranges are independent of the presentation of the overgroup. -/
theorem restrict_range_group_congr {G H J : Subgroup (GL (Fin 2) ℝ)}
    [G.HasDetOne] [H.HasDetOne] [J.HasDetOne] (k : ℤ)
    (hH : G ≤ H) (hJ : G ≤ J) (he : H = J) :
    LinearMap.range (restrict k hH) = LinearMap.range (restrict k hJ) := by
  subst J
  rfl

/-- The distinguished prime divisor of a level written as p²*L. -/
abbrev repeatedPrime (L p : ℕ) (hp : p.Prime) :
    {q : ℕ // q.Prime ∧ q ∣ p * (p * L)} :=
  ⟨p, hp, Nat.dvd_mul_right p (p * L)⟩

/-- Identification of the actual trace-old overlap with the lower-level
 cusp space at a repeated prime. -/
theorem primeOldIntersection_repeated_finrank (L p : ℕ) (hL : 0 < L) (hp : p.Prime)
    (hr : ((level (p * L)).relIndex (level L)).Prime) (k : ℤ) :
    Module.finrank ℂ (primeOldIntersection (p * (p * L))
      (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL)) k (repeatedPrime L p hp)) =
        Module.finrank ℂ (CuspForm (level L) k) := by
  have hd : p * (p * L) / p = p * L := Nat.mul_div_cancel_left (p * L) hp.pos
  have h1 := restrict_range_group_congr
    (G := level (p * (p * L))) (H := level (p * (p * L) / p)) (J := level (p * L)) k
    (level_antitone (Nat.div_dvd_of_dvd (Nat.dvd_mul_right p (p * L))))
    (level_antitone (Nat.dvd_mul_left (p * L) p)) (congrArg level hd)
  have hgroup : frickeOldLevel (p * (p * L)) (p * (p * L) / p)
      (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL)) = dilationLevel (p * L) p hp.pos := by
    exact (congrArg (fun d => frickeOldLevel (p * (p * L)) d
      (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL))) hd).trans
        (frickeOldLevel_eq_dilationLevel (p * L) p (Nat.mul_pos hp.pos hL) hp.pos)
  have h2 := restrict_range_group_congr
    (G := level (p * (p * L)))
    (H := frickeOldLevel (p * (p * L)) (p * (p * L) / p)
      (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL)))
    (J := dilationLevel (p * L) p hp.pos) k
    (level_le_frickeOldLevel (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL))
      (Nat.div_dvd_of_dvd (Nat.dvd_mul_right p (p * L))))
    (level_le_dilation_conjugate (p * L) p hp.pos) hgroup
  have hi := congrArg₂ (fun A B : Submodule ℂ (CuspForm (level (p * (p * L))) k) => A ⊓ B) h1 h2
  change primeOldIntersection (p * (p * L))
    (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL)) k (repeatedPrime L p hp) = _ at hi
  rw [hi]
  exact repeated_old_intersection_finrank L p hL hp hr k

/-- The exact classical second-difference formula for one repeated prime
 trace kernel. -/
theorem primeKernel_repeated_finrank (L p : ℕ) (hL : 0 < L) (hp : p.Prime)
    (hr : ((level (p * L)).relIndex (level L)).Prime) (k : ℤ) :
    Module.finrank ℂ (primeTraceKernel (p * (p * L))
      (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL)) k (repeatedPrime L p hp)) +
        2 * Module.finrank ℂ (CuspForm (level (p * L)) k) =
      Module.finrank ℂ (CuspForm (level (p * (p * L))) k) +
        Module.finrank ℂ (CuspForm (level L) k) := by
  have hh := primeKernel_finrank (p * (p * L))
    (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL)) k (repeatedPrime L p hp)
  rw [primeOldIntersection_repeated_finrank L p hL hp hr k] at hh
  dsimp only [repeatedPrime] at hh ⊢
  rw [Nat.mul_div_cancel_left (p * L) hp.pos] at hh
  exact hh

/-- At the only repeated prime allowed by admissibility, the intermediate
 index is always prime (two or three). -/
theorem two_lower_index_prime (L : ℕ) (hL : 0 < L) :
    ((level (2 * L)).relIndex (level L)).Prime := by
  rw [level_relIndex]
  by_cases h2 : 2 ∣ L
  · rw [AsymptoticRamifiedCosets.projective_index L 2 hL (by decide) h2]
    exact Nat.prime_two
  · rw [AsymptoticRamifiedCosets.projective_index_coprime L 2 hL Nat.prime_two
      (Nat.prime_two.coprime_iff_not_dvd.mpr h2)]
    norm_num

/-- The repeated-prime old/new dimension recurrence, with every arithmetic
 hypothesis discharged at p=2. -/
theorem twoKernel_finrank (L : ℕ) (hL : 0 < L) (k : ℤ) :
    Module.finrank ℂ (primeTraceKernel (2 * (2 * L))
      (by omega) k (repeatedPrime L 2 Nat.prime_two)) +
        2 * Module.finrank ℂ (CuspForm (level (2 * L)) k) =
      Module.finrank ℂ (CuspForm (level (2 * (2 * L))) k) +
        Module.finrank ℂ (CuspForm (level L) k) :=
  primeKernel_repeated_finrank L 2 hL Nat.prime_two (two_lower_index_prime L hL) k

#print axioms restrict_range_group_congr
#print axioms primeOldIntersection_repeated_finrank
#print axioms primeKernel_repeated_finrank
#print axioms two_lower_index_prime
#print axioms twoKernel_finrank

end AsymptoticClassicalCusp
