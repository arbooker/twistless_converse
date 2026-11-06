module

public import FinitenessAllLevelAlgebraicEliminantV1
public import Mathlib.FieldTheory.Perfect
public import Mathlib.Algebra.Squarefree.Basic

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelFiniteFiberAlgebra

open MvPolynomial

theorem map_aeval_variable {A B σ : Type*} [CommRing A] [CommRing B]
    (e : A →+* B) (i : σ) (q : Polynomial A) :
    MvPolynomial.map e (Polynomial.aeval (X i) q) =
      Polynomial.aeval (X i) (q.map e) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.map_add, hp, hq]
  | monomial n a => simp [Polynomial.aeval_monomial]

/-- Multiplicities can be removed over the coefficient fraction field and
denominators cleared. The resulting relation lies in the radical of the
original ideal, and its specialization at the injective parameter is
separable. Thus its roots there are genuinely simple. -/
theorem separable_coordinate_eliminant {A σ : Type*}
    [CommRing A] [IsDomain A] [CharZero A] [Finite σ]
    (e : A →+* ℂ) (he : Function.Injective e) (I : Ideal (MvPolynomial σ A))
    (hI : (zeroLocus ℂ (I.map (MvPolynomial.map e))).Finite) (i : σ) :
    ∃ q : Polynomial A, q ≠ 0 ∧ (q.map e).Separable ∧ Polynomial.aeval (X i) q ∈ I.radical := by
  classical
  obtain ⟨f, hf, hfI⟩ := coordinate_eliminant e he I hI i
  let K := FractionRing A
  let φ := algebraMap A K
  let E : K →+* ℂ := IsFractionRing.lift he
  have hE : E.comp φ = e := by ext a; exact IsFractionRing.lift_algebraMap he a
  let J := I.map (MvPolynomial.map φ)
  have hfk : f.map φ ≠ 0 := fun h => hf
    ((Polynomial.map_injective φ (IsFractionRing.injective A K)) (by simpa only [Polynomial.map_zero] using h))
  obtain ⟨y, n, hy, _, hdiv⟩ := exists_squarefree_dvd_pow_of_ne_zero hfk
  have hysep : y.Separable := PerfectField.separable_iff_squarefree.mpr hy
  have hyI : (Polynomial.aeval (X i) y) ^ n ∈ J := by
    obtain ⟨t, ht⟩ := hdiv
    have hh := Ideal.mem_map_of_mem (MvPolynomial.map φ) hfI
    rw [map_aeval_variable] at hh
    rw [← map_pow, ht, map_mul]
    exact J.mul_mem_right _ hh
  let q := IsLocalization.integerNormalization (nonZeroDivisors A) y
  obtain ⟨b, hb, hbq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A) y
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hqmap : q.map φ = Polynomial.C (φ b) * y := by
    calc
      q.map φ = b • y := hbq
      _ = (φ b) • y := (IsScalarTower.algebraMap_smul K b y).symm
      _ = Polynomial.C (φ b) * y := Polynomial.smul_eq_C_mul _
  have hqI : MvPolynomial.map φ ((Polynomial.aeval (X i) q) ^ n) ∈ J := by
    rw [map_pow, map_aeval_variable, hqmap, map_mul, Polynomial.aeval_C, mul_pow]
    exact J.mul_mem_left _ hyI
  let := MvPolynomial.algebraMvPolynomial (σ := σ) (R := A) (S := K)
  obtain ⟨s, hs, hsI⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    ((nonZeroDivisors A).map (MvPolynomial.C (σ := σ))) (MvPolynomial σ K) I
    ((Polynomial.aeval (X i) q) ^ n)).mp hqI
  obtain ⟨a, ha, rfl⟩ := hs
  have ha0 : a ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp ha
  have hqsep : (q.map e).Separable := by
    have hh := congrArg (Polynomial.map E) hqmap
    simp only [Polynomial.map_map, hE, Polynomial.map_mul, Polynomial.map_C] at hh
    rw [hh]
    apply Polynomial.Separable.unit_mul _ hysep.map
    apply (isUnit_iff_ne_zero.mpr ?_).map Polynomial.C
    exact (map_ne_zero_iff E E.injective).mpr ((map_ne_zero_iff φ
      (IsFractionRing.injective A K)).mpr hb0)
  have heqa : (Polynomial.C a * q).map e = Polynomial.C (e a) * q.map e := by simp
  have hsep : ((Polynomial.C a * q).map e).Separable := by
    rw [heqa]
    exact Polynomial.Separable.unit_mul ((isUnit_iff_ne_zero.mpr
      ((map_ne_zero_iff e he).mpr ha0)).map Polynomial.C) hqsep
  refine ⟨Polynomial.C a * q, fun h => hsep.ne_zero (by rw [h, Polynomial.map_zero]), hsep, ?_⟩
  apply Ideal.mem_radical_iff.mpr
  refine ⟨n + 1, ?_⟩
  have hh := I.mul_mem_left ((MvPolynomial.C a) ^ n * Polynomial.aeval (X i) q) hsI
  convert hh using 1
  simp only [map_mul, Polynomial.aeval_C, MvPolynomial.algebraMap_eq, mul_pow, pow_succ]
  ring

#print axioms map_aeval_variable
#print axioms separable_coordinate_eliminant

end FinitenessAllLevelFiniteFiberAlgebra
