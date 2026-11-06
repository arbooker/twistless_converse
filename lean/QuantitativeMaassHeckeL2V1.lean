module

public import QuantitativeMaassNormalizerL2V1
public import QuantitativeMaassFiniteCoverL2V1
public import AsymptoticClassicalPeterssonMeasureV1
public import AsymptoticClassicalHeckeNormalizerV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

open MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticClassicalCusp
open scoped ENNReal

namespace QuantitativeMaass

/-- The actual level-N automorphic Hilbert completion for hyperbolic quotient
measure. No spectral decomposition is part of this definition. -/
abbrev AutomorphicSpace (N : ℕ) := AutomorphicL2.space (gamma N) (quotientMeasure N)

namespace HeckeL2

variable (N p : ℕ) [Fact p.Prime] (hN : 0 < N) (hpN : ¬ p ∣ N)
    (A B : ℤ) (hAB : (p : ℤ)*A + (N : ℤ)*B = 1)

abbrev hp : 0 < p := (Fact.out : p.Prime).pos

noncomputable abbrev cosetFinite :
    Finite (gamma N ⧸ (gamma (p*N)).subgroupOf (gamma N)) :=
  Finite.of_equiv (Option (Fin p))
    (AsymptoticAtkinLehner.traceCosetEquiv N p hN hpN A B hAB)

/-- Literal pullback along the finite cover Γ0(pN)\H → Γ0(N)\H. -/
def inclusion : AutomorphicSpace N →L[ℂ] AutomorphicSpace (p*N) := by
  let := cosetFinite N p hN hpN A B hAB
  exact AutomorphicL2.coverOperator volume AsymptoticRationalGroup.measurePreserving
    (gamma (p*N)) (gamma N) (gamma_le_of_dvd (Nat.dvd_mul_left N p))
    (density N) (density (p*N)) (density_measurable N) (density_measurable (p*N))
    (density_orbit_sum N) (density_orbit_sum (p*N))

include hN hpN hAB in
theorem cover_index : ((gamma (p*N)).subgroupOf (gamma N)).index = p+1 := by
  have he := Nat.card_congr (AsymptoticAtkinLehner.traceCosetEquiv N p hN hpN A B hAB)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin,
    Subgroup.index] using he.symm

theorem inclusion_norm_le : ‖inclusion N p hN hpN A B hAB‖ ≤ Real.sqrt (p+1 : ℕ) := by
  let := cosetFinite N p hN hpN A B hAB
  have hi := AutomorphicL2.coverOperator_norm_le volume AsymptoticRationalGroup.measurePreserving
    (gamma (p*N)) (gamma N) (gamma_le_of_dvd (Nat.dvd_mul_left N p))
    (density N) (density (p*N)) (density_measurable N) (density_measurable (p*N))
    (density_orbit_sum N) (density_orbit_sum (p*N))
  rw [cover_index N p hN hpN A B hAB] at hi
  exact hi

/-- The actual rational determinant-p normalizer acting on the smaller-level
quotient Hilbert space, derived from its hyperbolic change of variables. -/
def normalizer : AutomorphicSpace (p*N) →ₗᵢ[ℂ] AutomorphicSpace (p*N) :=
  AutomorphicL2.normalizerIsometry volume AsymptoticRationalGroup.measurePreserving
    (gamma (p*N)) (heckeNormalizerLabel N p (hp p) A B hAB)
    (fun _ ha => heckeNormalizer_conj_mem N p (hp p) A B hAB hN ha)
    (fun _ ha => heckeNormalizer_inv_conj_mem N p (hp p) A B hAB hN ha)
    (density (p*N)) (density_measurable (p*N)) (density_orbit_sum (p*N))

/-- The bounded unramified Hecke correspondence on actual automorphic L²,
constructed as finite-cover pullback, the rational normalizer, and the
Hilbert adjoint pushforward. The branch formula is a separate theorem to
be proved, not an assumption in this construction. -/
def operator : AutomorphicSpace N →L[ℂ] AutomorphicSpace N :=
  (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) •
    ((inclusion N p hN hpN A B hAB).adjoint.comp
      ((normalizer N p hN A B hAB).toContinuousLinearMap.comp
        (inclusion N p hN hpN A B hAB)))

theorem operator_norm_le : ‖operator N p hN hpN A B hAB‖ ≤
    (p+1 : ℕ) / Real.sqrt (p : ℝ) := by
  let I := inclusion N p hN hpN A B hAB
  let U := (normalizer N p hN A B hAB).toContinuousLinearMap
  have hI : ‖I‖ ≤ Real.sqrt (p+1 : ℕ) := inclusion_norm_le N p hN hpN A B hAB
  have hU : ‖U‖ ≤ 1 := by
    apply U.opNorm_le_bound zero_le_one
    intro f
    change ‖normalizer N p hN A B hAB f‖ ≤ _
    simp only [LinearIsometry.norm_map, one_mul, le_refl]
  have hprod : ‖I.adjoint.comp (U.comp I)‖ ≤ (p+1 : ℕ) := by
    calc
      _ ≤ ‖I.adjoint‖ * (‖U‖ * ‖I‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ Real.sqrt (p+1 : ℕ) * (1 * Real.sqrt (p+1 : ℕ)) := by
        rw [ContinuousLinearMap.adjoint.norm_map]
        gcongr
      _ = (p+1 : ℕ) := by rw [one_mul, ← pow_two, Real.sq_sqrt (by positivity)]
  change ‖(((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) • (I.adjoint.comp (U.comp I))‖ ≤ _
  calc
    _ ≤ ‖(((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ)‖ * ‖I.adjoint.comp (U.comp I)‖ := ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ (Real.sqrt (p : ℝ))⁻¹ * (p+1 : ℕ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = _ := by ring

#print axioms inclusion_norm_le
#print axioms operator_norm_le

end HeckeL2
end QuantitativeMaass
