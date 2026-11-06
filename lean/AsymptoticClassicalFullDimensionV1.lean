module

public import AsymptoticClassicalCuspLowerDimensionV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalDimension

open UpperHalfPlane Filter Asymptotics AsymptoticSectorComparison
open AsymptoticClassicalCusp AsymptoticCongruenceStrip
open scoped MatrixGroups Topology

/-- A uniform bounded error for the total classical cusp dimension,
 derived from the discriminant injection and the Sturm bound. -/
theorem cusp_dimension_error (N : ℕ) (hN : 0 < N) (k : ℕ) (hk : Even k)
    (hlarge : 12 * (gamma N).relIndex (gamma 1) ≤ k) :
    |(Module.finrank ℂ (CuspForm (level N) (k : ℤ)) : ℝ) -
      ((gamma N).relIndex (gamma 1) : ℝ) * k / 12| ≤
      ((gamma N).relIndex (gamma 1) : ℝ) * ((gamma N).relIndex (gamma 1) + 1) + 1 := by
  let : NeZero N := ⟨hN.ne'⟩
  let I := (gamma N).relIndex (gamma 1)
  change 12 * I ≤ k at hlarge
  have hk' : Even (k - 12 * I) := by
    obtain ⟨m, hm⟩ := hk
    refine ⟨m - 6 * I, ?_⟩
    omega
  have hw : 12 * (I : ℤ) + ((k - 12 * I : ℕ) : ℤ) = (k : ℤ) := by
    omega
  have hl := cusp_dimension_lower N hN ((k - 12 * I : ℕ) : ℤ)
  change I * _ ≤ Module.finrank ℂ (CuspForm (level N) (12 * (I : ℤ) + _)) at hl
  rw [hw] at hl
  have hlR : (I : ℝ) * Module.finrank ℂ (ModularForm 𝒮ℒ ((k - 12 * I : ℕ) : ℤ)) ≤
      (Module.finrank ℂ (CuspForm (level N) (k : ℤ)) : ℝ) := by exact_mod_cast hl
  have hm := levelOne_modular_error (k - 12 * I) hk'
  rw [abs_le] at hm
  have hs : ((k - 12 * I : ℕ) : ℝ) = (k : ℝ) - 12 * (I : ℝ) := by
    rw [Nat.cast_sub hlarge, Nat.cast_mul]
    norm_num
  rw [hs] at hm
  have hu := cusp_dimension_le N (k : ℤ)
  have hnat : ((k : ℤ) * (I : ℤ)).toNat = k * I := by
    rw [← Nat.cast_mul, Int.toNat_natCast]
  change Module.finrank ℂ (CuspForm (level N) (k : ℤ)) ≤
    ((k : ℤ) * (I : ℤ)).toNat / 12 + 1 at hu
  rw [hnat] at hu
  have huR : (Module.finrank ℂ (CuspForm (level N) (k : ℤ)) : ℝ) ≤
      ((k * I / 12 : ℕ) : ℝ) + 1 := by exact_mod_cast hu
  have hfloor : ((k * I / 12 : ℕ) : ℝ) * 12 ≤ (k : ℝ) * I := by
    exact_mod_cast Nat.div_mul_le_self (k * I) 12
  have hI : (0 : ℝ) ≤ (I : ℝ) := Nat.cast_nonneg I
  change |(Module.finrank ℂ (CuspForm (level N) (k : ℤ)) : ℝ) - (I : ℝ) * k / 12| ≤
    (I : ℝ) * ((I : ℝ) + 1) + 1
  rw [abs_le]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hm.1 hI]

/-- The leading coefficient for the full cusp space at any positive
 level, with little-o error along even weights. -/
theorem cusp_dimension_littleO (N : ℕ) (hN : 0 < N) :
    (fun k : ℕ => (Module.finrank ℂ (CuspForm (level N) (k : ℤ)) : ℝ) -
      ((gamma N).relIndex (gamma 1) : ℝ) * k / 12)
      =o[evenWeights] (fun k => (k : ℝ)) := by
  apply bounded_error_littleO _
    (((gamma N).relIndex (gamma 1) : ℝ) * ((gamma N).relIndex (gamma 1) + 1) + 1)
  have hp : ∀ᶠ k in evenWeights, Even k :=
    Filter.Eventually.filter_mono inf_le_right (Filter.eventually_principal.mpr (fun _ h => h))
  have hl : ∀ᶠ k in evenWeights, 12 * (gamma N).relIndex (gamma 1) ≤ k :=
    (eventually_ge_atTop _).filter_mono inf_le_left
  filter_upwards [hp, hl] with k hk hl
  exact cusp_dimension_error N hN k hk hl

#print axioms cusp_dimension_error
#print axioms cusp_dimension_littleO

end AsymptoticClassicalDimension
