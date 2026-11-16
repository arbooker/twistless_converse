module

public import QuantitativeNinaMaassRamifiedTraceV1
public import QuantitativeNinaMaassFirstModeV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Set Matrix UpperHalfPlane QuantitativeMaass
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open AsymptoticClassicalDiscriminant
open scoped MatrixGroups

/-!
Literal Fourier action of the ramified upper correspondence. Its square
relation is proved in RamifiedTrace; here its height-dependent Fourier
relation is derived by integration. For actual joint eigenvectors, this
supplies every prime recurrence and proves that the first Fourier profile
cannot vanish. Existence of the joint spectral/all-prime eigenfamily and
separation of the Bessel amplitudes are still separate obligations.
-/

namespace QuantitativeNinaMaass

theorem triangular_upper_horocycle (p : ℕ) (hp : 0 < p) (a : ℤ)
    (x y : ℝ) (hy : 0 < y) :
    triangularGL 1 a p (by norm_num) (by exact_mod_cast hp) • horocyclePoint x y hy =
      horocyclePoint ((x + a) / p) (y / p)
        (div_pos hy (by exact_mod_cast hp)) := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos (by
    rw [triangularGL_det, one_mul]; exact_mod_cast hp), triangularGL_denom]
  simp only [UpperHalfPlane.num, triangularGL, horocyclePoint]
  apply Complex.ext <;> simp [Complex.div_re, Complex.div_im]
  all_goals field_simp

theorem normalizedUpperBranches_horocycle (p : ℕ) (hp : 0 < p) (f : ℍ → ℂ)
    (x y : ℝ) (hy : 0 < y) :
    normalizedUpperBranches p hp f (horocyclePoint x y hy) =
      (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) *
        ∑ a ∈ Finset.range p, f (horocyclePoint ((x + a) / p) (y / p)
          (div_pos hy (by exact_mod_cast hp))) := by
  unfold normalizedUpperBranches upperBranchSum
  congr 1
  calc
    _ = ∑ a : Fin p, f (horocyclePoint ((x + a.val) / p) (y / p)
        (div_pos hy (by exact_mod_cast hp))) := by
      apply Finset.sum_congr rfl
      intro a _
      simpa only [Int.cast_natCast] using congrArg f
        (triangular_upper_horocycle p hp (a.val : ℤ) x y hy)
    _ = _ := Fin.sum_univ_eq_sum_range (fun a : ℕ =>
      f (horocyclePoint ((x + a) / p) (y / p) (div_pos hy (by exact_mod_cast hp)))) p

theorem sqrt_normalization (p : ℕ) (hp : 0 < p) :
    (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) * (p : ℂ) = (Real.sqrt (p : ℝ) : ℂ) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hs : (Real.sqrt (p : ℝ))⁻¹ * (p : ℝ) = Real.sqrt (p : ℝ) := by
    calc
      _ = (Real.sqrt (p : ℝ))⁻¹ * (Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ)) :=
        congrArg (fun x : ℝ => (Real.sqrt (p : ℝ))⁻¹ * x) (Real.mul_self_sqrt hpR.le).symm
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (Real.sqrt_pos.mpr hpR).ne', one_mul]
  exact_mod_cast hs

/-- Unlike a good prime, the ramified correspondence has no downward
term. This follows from its actual p branches, with exact normalization. -/
theorem horocycleFourier_upper (p : ℕ) (hp : 0 < p) (f : ℍ → ℂ)
    (hf : Continuous f) (n : ℤ) (y : PositiveHeight) :
    horocycleFourier (normalizedUpperBranches p hp f) n y =
      (Real.sqrt (p : ℝ) : ℂ) * horocycleFourier f ((p : ℤ) * n) (divideHeight p hp y) := by
  let F : ℝ → ℂ := fun x => f (horocyclePoint x (y.val / p)
    (div_pos y.property (by exact_mod_cast hp)))
  have hF : Continuous F := hf.comp (horocyclePoint_continuous _ _)
  have hshape : (fun x => normalizedUpperBranches p hp f (horocyclePoint x y.val y.property)) =
      fun x => (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) *
        ∑ a ∈ Finset.range p, F ((x + a) / p) := by
    funext x
    exact normalizedUpperBranches_horocycle p hp f x y.val y.property
  unfold horocycleFourier
  rw [hshape, unitLineFourierCoeff_const_mul,
    unitLineFourierCoeff_inverse_branch_sum F hF p hp, ← mul_assoc, sqrt_normalization p hp]
  rfl

theorem horocycleFourier_upper_eigen (p : ℕ) (hp : 0 < p) (f : ℍ → ℂ)
    (hf : Continuous f) (ell : ℂ)
    (he : normalizedUpperBranches p hp f = fun z => ell * f z)
    (n : ℤ) (y : PositiveHeight) :
    ell * horocycleFourier f n y =
      (Real.sqrt (p : ℝ) : ℂ) * horocycleFourier f ((p : ℤ) * n) (divideHeight p hp y) := by
  have h := horocycleFourier_upper p hp f hf n y
  rwa [he, horocycleFourier_const_mul] at h

/-- The Fourier action is also an endomorphism on the actual height
profiles. This identity can be used to establish physical commutation. -/
theorem actualHeightCoefficients_upper (p : ℕ) (hp : 0 < p) (f : ℍ → ℂ)
    (hf : Continuous f) :
    actualHeightCoefficients (normalizedUpperBranches p hp f) =
      (Real.sqrt (p : ℝ) : ℂ) • heightUp p hp (actualHeightCoefficients f) := by
  funext n y
  simpa only [actualHeightCoefficients, heightUp, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.smul_apply, smul_eq_mul, Nat.cast_mul] using horocycleFourier_upper p hp f hf n y

theorem good_prime_height_eigenrelation (N p : ℕ) [Fact p.Prime]
    (hN : 0 < N) (hpN : ¬ p ∣ N) (hNp : (N : ZMod p) ≠ 0)
    (A B : ℤ) (hAB : (p : ℤ) * A + (N : ℤ) * B = 1)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (ell : ℂ)
    (he : HeckeL2.operator N p hN hpN A B hAB (AutomorphicL2.denseEmbedding _ _ f) =
      ell • AutomorphicL2.denseEmbedding _ _ f) (n : ℕ) (y : PositiveHeight) :
    ell * actualHeightCoefficients f.val n y =
      (Real.sqrt (p : ℝ) : ℂ) *
        actualHeightCoefficients f.val (p * n) (divideHeight p (Fact.out : p.Prime).pos y) +
      if p ∣ n then (Real.sqrt (p : ℝ) : ℂ)⁻¹ *
        actualHeightCoefficients f.val (n / p) (multiplyHeight p (Fact.out : p.Prime).pos y)
        else 0 := by
  have h := actualHeightCoefficients_hecke N p hN hpN hNp A B hAB f hf
  rw [hecke_eigen_representative N p hN hpN hNp A B hAB f hf ell he] at h
  have hh := congrFun (congrFun h n) y
  change horocycleFourier (fun z => ell * f.val z) n y = _ at hh
  rw [horocycleFourier_const_mul] at hh
  change ell * actualHeightCoefficients f.val n y = _ at hh
  rw [hh]
  have hs : (Real.sqrt (p : ℝ) : ℂ)⁻¹ * (p : ℂ) = (Real.sqrt (p : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_inv] using sqrt_normalization p (Fact.out : p.Prime).pos
  simp only [heightHecke, LinearMap.add_apply, LinearMap.smul_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, heightUp, heightDown, LinearMap.coe_mk, AddHom.coe_mk,
    Complex.ofReal_inv, hs]
  split_ifs <;> ring

/-- The assumptions are concrete eigenrelations for physical operators.
All prime coefficient recurrences are conclusions of the Fourier integrals. -/
theorem physical_prime_height_relations (N : ℕ) (hN : 0 < N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (ell : ℕ → ℂ)
    (hgood : ∀ (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N),
      let : Fact p.Prime := ⟨hp⟩
      ∀ (A B : ℤ) (hAB : (p : ℤ) * A + (N : ℤ) * B = 1),
        HeckeL2.operator N p hN hpN A B hAB (AutomorphicL2.denseEmbedding _ _ f) =
          ell p • AutomorphicL2.denseEmbedding _ _ f)
    (hbad : ∀ (p : ℕ) (hp : p.Prime), p ∣ N →
      normalizedUpperBranches p hp.pos f.val = fun z => ell p * f.val z) :
    PrimeHeightEigenrelations N ell (actualHeightCoefficients f.val) := by
  intro p hp n y
  by_cases hpN : p ∣ N
  · have h := horocycleFourier_upper_eigen p hp.pos f.val hf (ell p) (hbad p hp hpN) n y
    simpa only [actualHeightCoefficients, Nat.cast_mul, hpN, not_true_eq_false,
      false_and, ite_false, add_zero] using h
  · let : Fact p.Prime := ⟨hp⟩
    have hc : p.Coprime N := hp.coprime_iff_not_dvd.mpr hpN
    have hAB : (p : ℤ) * Nat.gcdA p N + (N : ℤ) * Nat.gcdB p N = 1 := by
      have h := Nat.gcd_eq_gcd_ab p N
      rw [hc.gcd_eq_one, Nat.cast_one] at h
      exact h.symm
    have hNp : (N : ZMod p) ≠ 0 := fun h => hpN ((ZMod.natCast_eq_zero_iff N p).mp h)
    simpa only [hpN, not_false_eq_true, true_and] using
      good_prime_height_eigenrelation N p hN hpN hNp _ _ hAB f hf (ell p)
        (hgood p hp hpN _ _ hAB) n y

/-- An actual nonzero cusp eigenfunction satisfying the concrete prime
relations has a nonzero first Fourier profile. No multiplicity-one premise
or nonvanishing coefficient assumption is needed for this implication. -/
theorem physical_first_profile_nonzero (N : ℕ) (hN : 0 < N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (hf0 : f ≠ 0)
    (hcf : AutomorphicL2.denseEmbedding _ _ f ∈ localCuspidalSpace N hN)
    (s : ℂ)
    (hsf : reflectionIsometry N (AutomorphicL2.denseEmbedding _ _ f) =
      s • AutomorphicL2.denseEmbedding _ _ f)
    (ell : ℕ → ℂ) (hr : PrimeHeightEigenrelations N ell (actualHeightCoefficients f.val)) :
    ∃ y : PositiveHeight, horocycleFourier f.val 1 y ≠ 0 := by
  by_contra! hz
  have hzero := prime_height_first_zero N ell (actualHeightCoefficients f.val) hr hz
  apply hf0
  apply physical_positive_coefficients_separate N hN f 0 hf continuous_const hcf
    (by simpa only [map_zero] using (localCuspidalSpace N hN).zero_mem) s hsf
    (by simp only [map_zero, smul_zero])
  funext n y
  have h := hzero (n + 1) (by omega) y
  change _ = unitLineFourierCoeff (fun _ : ℝ => 0) (n + 1)
  simpa only [positiveHorocycleCoefficients, actualHeightCoefficients, horocycleFourier,
    Nat.cast_add, Nat.cast_one, unitLineFourierCoeff, mul_zero, intervalIntegral.integral_zero]
    using h

#print axioms triangular_upper_horocycle
#print axioms normalizedUpperBranches_horocycle
#print axioms sqrt_normalization
#print axioms horocycleFourier_upper
#print axioms horocycleFourier_upper_eigen
#print axioms actualHeightCoefficients_upper
#print axioms good_prime_height_eigenrelation
#print axioms physical_prime_height_relations
#print axioms physical_first_profile_nonzero

end QuantitativeNinaMaass
