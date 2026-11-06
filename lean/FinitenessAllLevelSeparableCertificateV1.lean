module

public import FinitenessAllLevelSeparableEliminantV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelFiniteFiberAlgebra

/-- A separable injective specialization has a Bezout certificate over the
original coefficient domain, with one nonzero scalar denominator. -/
theorem separable_certificate {A : Type*} [CommRing A] [IsDomain A]
    (e : A →+* ℂ) (he : Function.Injective e) (q : Polynomial A)
    (hs : (q.map e).Separable) :
    ∃ c : A, c ≠ 0 ∧ ∃ u v : Polynomial A,
      u * q + v * q.derivative = Polynomial.C c := by
  let K := FractionRing A
  let φ := algebraMap A K
  let E : K →+* ℂ := IsFractionRing.lift he
  have hE : E.comp φ = e := by ext a; exact IsFractionRing.lift_algebraMap he a
  have hsep : (q.map φ).Separable := by
    apply (Polynomial.separable_map E).mp
    simpa only [Polynomial.map_map, hE] using hs
  obtain ⟨r, s, hrs⟩ := (Polynomial.separable_def' _).mp hsep
  let u := IsLocalization.integerNormalization (nonZeroDivisors A) r
  let v := IsLocalization.integerNormalization (nonZeroDivisors A) s
  obtain ⟨b, hb, hbu⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A) r
  obtain ⟨d, hd, hdv⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A) s
  have hu : u.map φ = Polynomial.C (φ b) * r := by
    calc
      u.map φ = b • r := hbu
      _ = (φ b) • r := (IsScalarTower.algebraMap_smul K b r).symm
      _ = Polynomial.C (φ b) * r := Polynomial.smul_eq_C_mul _
  have hv : v.map φ = Polynomial.C (φ d) * s := by
    calc
      v.map φ = d • s := hdv
      _ = (φ d) • s := (IsScalarTower.algebraMap_smul K d s).symm
      _ = Polynomial.C (φ d) * s := Polynomial.smul_eq_C_mul _
  refine ⟨b * d, mul_ne_zero (mem_nonZeroDivisors_iff_ne_zero.mp hb)
    (mem_nonZeroDivisors_iff_ne_zero.mp hd), Polynomial.C d * u, Polynomial.C b * v, ?_⟩
  apply Polynomial.map_injective φ (IsFractionRing.injective A K)
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hu, hv,
    ← Polynomial.derivative_map, map_mul]
  calc
    _ = Polynomial.C (φ b) * Polynomial.C (φ d) *
        (r * q.map φ + s * (q.map φ).derivative) := by ring
    _ = Polynomial.C (φ b) * Polynomial.C (φ d) := by rw [hrs, mul_one]

/-- Every specialization away from the single certificate scalar is separable. -/
theorem separable_of_certificate {A B : Type*} [CommRing A] [Field B]
    (q : Polynomial A) (c : A) (u v : Polynomial A)
    (hcert : u * q + v * q.derivative = Polynomial.C c)
    (e : A →+* B) (hc : e c ≠ 0) : (q.map e).Separable := by
  apply (Polynomial.separable_def' _).mpr
  refine ⟨Polynomial.C (e c)⁻¹ * u.map e, Polynomial.C (e c)⁻¹ * v.map e, ?_⟩
  have h := congrArg (Polynomial.map e) hcert
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
    ← Polynomial.derivative_map] at h
  calc
    _ = Polynomial.C (e c)⁻¹ * (u.map e * q.map e + v.map e * (q.map e).derivative) := by ring
    _ = 1 := by rw [h, ← Polynomial.C_mul, inv_mul_cancel₀ hc, Polynomial.C_1]

#print axioms separable_certificate
#print axioms separable_of_certificate

end FinitenessAllLevelFiniteFiberAlgebra
