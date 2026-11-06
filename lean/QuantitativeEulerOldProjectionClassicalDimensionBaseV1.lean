module

public import AsymptoticClassicalNewDimensionBasesV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section

namespace QuantitativeEulerOldProjectionClassicalDimension

open UpperHalfPlane Filter AsymptoticSectorComparison AsymptoticClassicalCusp
open AsymptoticClassicalDimension AsymptoticCongruenceStrip

/-- Retain the bounded full-cusp dimension remainder, rather than losing
its rate when passing to a little-o statement. -/
theorem full_dimension_bounded (N : ℕ) (hN : 0 < N) :
    ∃ C : ℝ, ∀ᶠ k : ℕ in evenWeights,
      |(Module.finrank ℂ (CuspForm (level N) (k : ℤ)) : ℝ) - fullLeading N * k| ≤ C := by
  refine ⟨((gamma N).relIndex (gamma 1) : ℝ) *
    ((gamma N).relIndex (gamma 1) + 1) + 1, ?_⟩
  have hp : ∀ᶠ k in evenWeights, Even k :=
    Filter.Eventually.filter_mono inf_le_right (Filter.eventually_principal.mpr (fun _ h => h))
  have hl : ∀ᶠ k in evenWeights, 12 * (gamma N).relIndex (gamma 1) ≤ k :=
    (eventually_ge_atTop _).filter_mono inf_le_left
  filter_upwards [hp, hl] with k hk hl
  simpa only [fullLeading, div_mul_eq_mul_div] using cusp_dimension_error N hN k hk hl

theorem empty_dimension_bounded (N : ℕ) (hN : 0 < N) :
    ∃ C : ℝ, ∀ᶠ k : ℕ in evenWeights,
      |(Module.finrank ℂ (partialNewSpace N hN (k : ℤ) ∅) : ℝ) - fullLeading N * k| ≤ C := by
  obtain ⟨C, hC⟩ := full_dimension_bounded N hN
  refine ⟨C, ?_⟩
  have hd (k : ℕ) : Module.finrank ℂ (partialNewSpace N hN (k : ℤ) ∅) =
      Module.finrank ℂ (CuspForm (level N) (k : ℤ)) := by
    rw [partialNewSpace_empty, finrank_top]
  simpa only [hd] using hC

/-- The exact repeated-two dimension recurrence preserves a bounded error
with constant B(4L)+2B(2L)+B(L). -/
theorem twoKernel_dimension_bounded (L : ℕ) (hL : 0 < L) :
    ∃ C : ℝ, ∀ᶠ k : ℕ in evenWeights,
      |(Module.finrank ℂ (primeTraceKernel (2 * (2 * L)) (by omega) (k : ℤ)
        (repeatedPrime L 2 Nat.prime_two)) : ℝ) -
      (((gamma (2 * (2 * L))).relIndex (gamma 1) : ℝ) -
        2 * ((gamma (2 * L)).relIndex (gamma 1) : ℝ) +
        ((gamma L).relIndex (gamma 1) : ℝ)) * k / 12| ≤ C := by
  let I (N : ℕ) : ℝ := (gamma N).relIndex (gamma 1)
  let B (N : ℕ) : ℝ := I N * (I N + 1) + 1
  refine ⟨B (2 * (2 * L)) + 2 * B (2 * L) + B L, ?_⟩
  have hp : ∀ᶠ k in evenWeights, Even k :=
    Filter.Eventually.filter_mono inf_le_right (Filter.eventually_principal.mpr (fun _ h => h))
  have hlarge (N : ℕ) : ∀ᶠ k in evenWeights,
      12 * (gamma N).relIndex (gamma 1) ≤ k :=
    (eventually_ge_atTop _).filter_mono inf_le_left
  filter_upwards [hp, hlarge (2 * (2 * L)), hlarge (2 * L), hlarge L] with k hk hN hM hL'
  have htop := cusp_dimension_error (2 * (2 * L)) (by omega) k hk hN
  have hmid := cusp_dimension_error (2 * L) (by omega) k hk hM
  have hbot := cusp_dimension_error L hL k hk hL'
  have he := twoKernel_finrank L hL (k : ℤ)
  have heR :
      (Module.finrank ℂ (primeTraceKernel (2 * (2 * L)) (by omega) (k : ℤ)
        (repeatedPrime L 2 Nat.prime_two)) : ℝ) +
        2 * (Module.finrank ℂ (CuspForm (level (2 * L)) (k : ℤ)) : ℝ) =
      (Module.finrank ℂ (CuspForm (level (2 * (2 * L))) (k : ℤ)) : ℝ) +
        (Module.finrank ℂ (CuspForm (level L) (k : ℤ)) : ℝ) := by exact_mod_cast he
  change |_ - (I (2 * (2 * L)) - 2 * I (2 * L) + I L) * (k : ℝ) / 12| ≤ _
  change |_ - I (2 * (2 * L)) * (k : ℝ) / 12| ≤ B (2 * (2 * L)) at htop
  change |_ - I (2 * L) * (k : ℝ) / 12| ≤ B (2 * L) at hmid
  change |_ - I L * (k : ℝ) / 12| ≤ B L at hbot
  rw [abs_le] at htop hmid hbot ⊢
  constructor <;> nlinarith [htop.1, htop.2, hmid.1, hmid.2, hbot.1, hbot.2]

theorem two_dimension_bounded (N : ℕ) (hN : 0 < N) (h4 : 4 ∣ N) :
    ∃ C : ℝ, ∀ᶠ k : ℕ in evenWeights,
      |(Module.finrank ℂ (partialNewSpace N hN (k : ℤ) {2}) : ℝ) - twoLeading N * k| ≤ C := by
  obtain ⟨L, hNL⟩ := h4
  have heN : N = 2 * (2 * L) := by omega
  clear hNL
  subst N
  have hL : 0 < L := by omega
  have he : 4 * L = 2 * (2 * L) := by omega
  have hd2 : 2 * (2 * L) / 2 = 2 * L := Nat.mul_div_cancel_left _ (by decide)
  have hd4 : 2 * (2 * L) / 4 = L := by rw [← he]; exact Nat.mul_div_cancel_left _ (by decide)
  obtain ⟨C, hh⟩ := twoKernel_dimension_bounded L hL
  refine ⟨C, ?_⟩
  have hs (k : ℕ) : partialNewSpace (2 * (2 * L)) (by omega) (k : ℤ) {2} =
      primeTraceKernel (2 * (2 * L)) (by omega) (k : ℤ) (repeatedPrime L 2 Nat.prime_two) :=
    partialNewSpace_singleton _ _ _ (repeatedPrime L 2 Nat.prime_two)
  have hdim (k : ℕ) := congrArg
    (fun U : Submodule ℂ (CuspForm (level (2 * (2 * L))) (k : ℤ)) => Module.finrank ℂ U) (hs k)
  simp_rw [← hdim] at hh
  simpa only [twoLeading, hd2, hd4, div_mul_eq_mul_div] using hh

#print axioms full_dimension_bounded
#print axioms two_dimension_bounded
end QuantitativeEulerOldProjectionClassicalDimension
