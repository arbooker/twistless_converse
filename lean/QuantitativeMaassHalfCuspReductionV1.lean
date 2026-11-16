module

public import QuantitativeMaassHalfTranslationNormalizerV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Matrix UpperHalfPlane AsymptoticCongruenceLabels AsymptoticIntegralSubgroup
open AsymptoticRationalGroup AsymptoticRationalFreeness AsymptoticFreshMatrices
open scoped MatrixGroups

namespace QuantitativeMaass

/-- If the cusp denominator has exactly one factor of two, a
half-translation has a primitive integral chart with odd denominator. -/
def halfCuspReduction (a : SL(2,ℤ)) (c u : ℤ)
    (hc : a 1 0=2*c) (hu : a 0 0+c=2*u) : SL(2,ℤ) :=
  ⟨!![u,a 1 1+2*a 0 1;c,2*a 1 1],by
    rw [Matrix.det_fin_two]
    dsimp
    have hd := a.property
    rw [Matrix.det_fin_two] at hd
    change a 0 0*a 1 1-a 0 1*a 1 0=1 at hd
    rw [hc] at hd
    linear_combination hd-(a 1 1)*hu⟩

theorem halfCuspReduction_exists (a : SL(2,ℤ)) (h2 : (2:ℤ)∣a 1 0)
    (h4 : ¬(4:ℤ)∣a 1 0) :
    ∃ c u : ℤ,a 1 0=2*c ∧ a 0 0+c=2*u ∧ ¬(2:ℤ)∣c := by
  obtain ⟨c,hc⟩ := h2
  have hc2 : ¬(2:ℤ)∣c := by
    intro h
    apply h4
    obtain ⟨d,hd⟩ := h
    exact ⟨d,by rw [hc,hd]; ring⟩
  have hd := a.property
  rw [Matrix.det_fin_two] at hd
  change a 0 0*a 1 1-a 0 1*a 1 0=1 at hd
  have ho : Odd (a 0 0*a 1 1) := ⟨a 0 1*c,by rw [hc] at hd; linear_combination hd⟩
  have haodd := (Int.odd_mul.mp ho).1
  have hcodd : Odd c := Int.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using hc2)
  obtain ⟨s,hs⟩ := haodd
  obtain ⟨t,ht⟩ := hcodd
  exact ⟨c,s+t+1,hc,by rw [hs,ht]; ring,hc2⟩

theorem halfCuspReduction_label (a : SL(2,ℤ)) (c u : ℤ)
    (hc : a 1 0=2*c) (hu : a 0 0+c=2*u) :
    translationLabel (1/2)*integralLabel a=
      integralLabel (halfCuspReduction a c u hc hu)*dilationLabel 4 (by decide) := by
  have hcr : (a 1 0:ℚ)=2*c := by exact_mod_cast hc
  have hur : (a 0 0:ℚ)+(c:ℚ)=2*u := by exact_mod_cast hu
  have he : AsymptoticMobiusFold.translation (1/2)*rationalGL a=
      (rationalGL (halfCuspReduction a c u hc hu)*dilationGL 4 (by decide))*
        GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (1/2:ℚ) (by norm_num)) := by
    apply Units.ext
    change (AsymptoticMobiusFold.translation (1/2)).val*(rationalGL a).val=
      ((rationalGL (halfCuspReduction a c u hc hu)).val*(dilationGL 4 (by decide)).val)*
        (GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (1/2:ℚ) (by norm_num))).val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [AsymptoticMobiusFold.translation,rationalGL_apply,halfCuspReduction,
        dilationGL,GeneralLinearGroup.mkOfDetNeZero,GeneralLinearGroup.scalar,
        Matrix.scalar,Matrix.algebraMap_eq_diagonal,Matrix.diagonal,Matrix.mul_apply,Fin.sum_univ_two,hcr]
    all_goals first | (solve | ring) | linear_combination hur
  apply Subtype.ext
  apply Subtype.ext
  change rationalMap (AsymptoticMobiusFold.translation (1/2))*rationalMap (rationalGL a)=
    rationalMap (rationalGL (halfCuspReduction a c u hc hu))*rationalMap (dilationGL 4 (by decide))
  rw [←map_mul,he,map_mul,rationalMap_scalar,mul_one,map_mul]

#print axioms halfCuspReduction_exists
#print axioms halfCuspReduction_label

end QuantitativeMaass
