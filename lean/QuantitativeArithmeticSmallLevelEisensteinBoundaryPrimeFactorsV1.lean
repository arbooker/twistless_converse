module

public import QuantitativeArithmeticSmallLevelEisensteinBoundaryIntegralV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelEisenstein

open Matrix UpperHalfPlane Filter AsymptoticClassicalDiscriminant
open scoped MatrixGroups ModularForm

theorem prime_positive_factors (p : ℕ) (hp : p.Prime) (a d : ℤ)
    (ha : 0<a) (hd : 0<d) (had : a*d=p) :
    (a=1 ∧ d=p) ∨ (a=p ∧ d=1) := by
  have haN : (a.toNat : ℤ)=a := Int.toNat_of_nonneg ha.le
  have hdN : (d.toNat : ℤ)=d := Int.toNat_of_nonneg hd.le
  have hN : a.toNat*d.toNat=p := by exact_mod_cast (by simpa only [Nat.cast_mul,haN,hdN] using had : ((a.toNat*d.toNat : ℕ) : ℤ) = p)
  have hav : a.toNat∣p := ⟨d.toNat,hN.symm⟩
  rcases (Nat.dvd_prime hp).mp hav with h1 | hp'
  · left
    have he : a=1 := by rw [← haN,h1]; rfl
    exact ⟨he,by simpa only [he,one_mul] using had⟩
  · right
    have he : a=(p:ℤ) := by rw [← haN,hp']
    refine ⟨he,?_⟩
    have hpZ : (0:ℤ)<p := by exact_mod_cast hp.pos
    nlinarith [had]

/-- The expanding triangular diagonal is detected solely by divisibility
of the original integral first column. -/
theorem prime_reduction_expanding_iff (p : ℕ) (hp : p.Prime)
    (B : Matrix (Fin 2) (Fin 2) ℤ) (U : SL(2,ℤ)) (a d : ℤ)
    (ha : 0<a) (hd : 0<d) (had : a*d=p)
    (hcol : ∀ i : Fin 2, B i 0 = U i 0*a) :
    a=p ↔ (p:ℤ)∣B 0 0 ∧ (p:ℤ)∣B 1 0 := by
  constructor
  · intro he
    constructor <;> rw [hcol,he] <;> exact dvd_mul_left _ _
  · rintro ⟨h0,h1⟩
    rcases prime_positive_factors p hp a d ha hd had with ⟨ha1,_⟩ | ⟨hap,_⟩
    · have hu0 : (p:ℤ)∣U 0 0 := by simpa only [hcol,ha1,mul_one] using h0
      have hu1 : (p:ℤ)∣U 1 0 := by simpa only [hcol,ha1,mul_one] using h1
      have hdiv : (p:ℤ)∣U 0 0*U 1 1-U 0 1*U 1 0 :=
        dvd_sub (dvd_mul_of_dvd_left hu0 _) (dvd_mul_of_dvd_right hu1 _)
      have hdet := U.property
      rw [Matrix.det_fin_two] at hdet
      rw [hdet] at hdiv
      have hle := Int.le_of_dvd (by norm_num : (0:ℤ)<1) hdiv
      have hgt : (1:ℤ)<p := by exact_mod_cast hp.one_lt
      omega
    · exact hap

theorem prime_reduction_factor (p : ℕ) (hp : p.Prime)
    (B : Matrix (Fin 2) (Fin 2) ℤ) (U : SL(2,ℤ)) (a d : ℤ)
    (ha : 0<a) (hd : 0<d) (had : a*d=p)
    (hcol : ∀ i : Fin 2, B i 0 = U i 0*a) (k : ℤ) :
    triangularFactor (a:ℝ) (d:ℝ) k =
      if (p:ℤ)∣B 0 0 ∧ (p:ℤ)∣B 1 0 then (p:ℂ)^(k-1) else (p:ℂ)⁻¹ := by
  by_cases hb : (p:ℤ)∣B 0 0 ∧ (p:ℤ)∣B 1 0
  · have hap := (prime_reduction_expanding_iff p hp B U a d ha hd had hcol).mpr hb
    have hd1 : d=1 := by
      have hpZ : (0:ℤ)<p := by exact_mod_cast hp.pos
      nlinarith [had]
    simpa only [hap,hd1,ite_eq_left hb,Int.cast_one,Int.cast_natCast] using
      (triangularFactor_prime p hp.pos k).2
  · rcases prime_positive_factors p hp a d ha hd had with ⟨ha1,hdp⟩ | ⟨hap,_⟩
    · simpa only [ha1,hdp,ite_eq_right hb,Int.cast_one,Int.cast_natCast] using
        (triangularFactor_prime p hp.pos k).1
    · exact False.elim (hb ((prime_reduction_expanding_iff p hp B U a d ha hd had hcol).mp hap))

#print axioms prime_positive_factors
#print axioms prime_reduction_expanding_iff
#print axioms prime_reduction_factor

end QuantitativeArithmeticSmallLevelEisenstein
