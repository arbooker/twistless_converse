module

public import AsymptoticClassicalFiniteDimensionV1
public import AsymptoticSectorComparisonV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalDimension

open UpperHalfPlane Filter Asymptotics AsymptoticSectorComparison
open scoped MatrixGroups Topology

/-- The existing level-one rank formula, expressed as a finite dimension. -/
theorem levelOne_modular_finrank (k : ℕ) (hk : Even k) :
    Module.finrank ℂ (ModularForm 𝒮ℒ (k : ℤ)) =
      if k ≡ 2 [MOD 12] then k / 12 else k / 12 + 1 := by
  have hh := ModularForm.dimension_level_one k hk
  split_ifs at hh ⊢ with h
  · exact Module.finrank_eq_of_rank_eq hh
  · exact Module.finrank_eq_of_rank_eq (by simpa using hh)

/-- Uniform bounded error for the classical level-one full modular space. -/
theorem levelOne_modular_error (k : ℕ) (hk : Even k) :
    |(Module.finrank ℂ (ModularForm 𝒮ℒ (k : ℤ)) : ℝ) - (k : ℝ) / 12| ≤ 1 := by
  have hq : ((k % 12 : ℕ) : ℝ) + 12 * (k / 12 : ℕ) = (k : ℝ) := by
    exact_mod_cast Nat.mod_add_div k 12
  have hr : ((k % 12 : ℕ) : ℝ) < 12 := by exact_mod_cast Nat.mod_lt k (by decide : 0 < 12)
  have hp : (0 : ℝ) ≤ ((k % 12 : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [levelOne_modular_finrank k hk]
  split_ifs <;> simp only [Nat.cast_add, Nat.cast_one, abs_le] <;>
    constructor <;> linarith

/-- The cusp dimension differs from k/12 by a bounded amount. This is a
 classical total-space statement, with no sign-sector dimensions. -/
theorem levelOne_cusp_error (k : ℕ) (hk : Even k) (hlarge : 12 ≤ k) :
    |(Module.finrank ℂ (CuspForm 𝒮ℒ (k : ℤ)) : ℝ) - (k : ℝ) / 12| ≤ 2 := by
  have he : Module.finrank ℂ (CuspForm 𝒮ℒ (k : ℤ)) =
      Module.finrank ℂ (ModularForm 𝒮ℒ ((k - 12 : ℕ) : ℤ)) := by
    have hsI : ((k - 12 : ℕ) : ℤ) = (k : ℤ) - 12 := by omega
    rw [hsI]
    exact (CuspForm.discriminantEquiv (k := (k : ℤ))).finrank_eq
  have hk' : Even (k - 12) := by
    obtain ⟨m, hm⟩ := hk
    refine ⟨m - 6, ?_⟩
    omega
  have hh := levelOne_modular_error (k - 12) hk'
  have hs : ((k - 12 : ℕ) : ℝ) = (k : ℝ) - 12 := by
    rw [Nat.cast_sub hlarge]
    norm_num
  rw [he, abs_le]
  rw [abs_le, hs] at hh
  constructor <;> linarith

/-- A bounded real error is negligible relative to the growing weight. -/
theorem bounded_error_littleO (e : ℕ → ℝ) (C : ℝ)
    (he : ∀ᶠ k in evenWeights, |e k| ≤ C) :
    e =o[evenWeights] (fun k => (k : ℝ)) := by
  apply IsLittleO.of_bound
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_gt (C / ε)
  have hlarge : ∀ᶠ k in evenWeights, m ≤ k :=
    (eventually_ge_atTop m).filter_mono inf_le_left
  filter_upwards [he, hlarge] with k he hk
  have hmk : (m : ℝ) ≤ k := by exact_mod_cast hk
  have hc : C ≤ ε * (k : ℝ) := by
    have := (div_lt_iff₀ hε).mp hm
    nlinarith
  simpa only [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k)] using he.trans hc

theorem levelOne_cusp_littleO :
    (fun k : ℕ => (Module.finrank ℂ (CuspForm 𝒮ℒ (k : ℤ)) : ℝ) - (k : ℝ) / 12)
      =o[evenWeights] (fun k => (k : ℝ)) := by
  apply bounded_error_littleO _ 2
  have hp : ∀ᶠ k in evenWeights, Even k :=
    Filter.Eventually.filter_mono inf_le_right (Filter.eventually_principal.mpr (fun _ h => h))
  have hl : ∀ᶠ k in evenWeights, 12 ≤ k :=
    (eventually_ge_atTop 12).filter_mono inf_le_left
  filter_upwards [hp, hl] with k hk hl
  exact levelOne_cusp_error k hk hl

#print axioms levelOne_modular_finrank
#print axioms levelOne_modular_error
#print axioms levelOne_cusp_error
#print axioms bounded_error_littleO
#print axioms levelOne_cusp_littleO

end AsymptoticClassicalDimension
