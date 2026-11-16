module

public import AsymptoticAtkinLehnerNormalizerV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Matrix AsymptoticRationalGroup AsymptoticRationalFreeness
open AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open AsymptoticIntegralSubgroup
open scoped MatrixGroups

namespace QuantitativeMaass

/-- The diagonal entries of an integral determinant-one matrix whose lower
left entry is divisible by four have the same parity. -/
theorem halfTranslation_diagonal_difference (a : SL(2,ℤ)) (c : ℤ)
    (hc : a 1 0=4*c) : ∃ r : ℤ,a 1 1-a 0 0=2*r := by
  have hd := a.property
  rw [Matrix.det_fin_two] at hd
  change a 0 0*a 1 1-a 0 1*a 1 0=1 at hd
  have ho : Odd (a 0 0*a 1 1) := by
    refine ⟨2*a 0 1*c,?_⟩
    rw [hc] at hd
    linear_combination hd
  obtain ⟨u,hu⟩ := (Int.odd_mul.mp ho).1
  obtain ⟨v,hv⟩ := (Int.odd_mul.mp ho).2
  exact ⟨v-u,by rw [hu,hv]; ring⟩

def halfTranslationConjugate (n : ℤ) (a : SL(2,ℤ)) (c r : ℤ)
    (hc : a 1 0=4*c) (hr : a 1 1-a 0 0=2*r) : SL(2,ℤ) :=
  ⟨!![a 0 0+2*n*c,a 0 1+n*r-n^2*c;4*c,a 1 1-2*n*c],by
    rw [Matrix.det_fin_two]
    dsimp
    have hd := a.property
    rw [Matrix.det_fin_two] at hd
    change a 0 0*a 1 1-a 0 1*a 1 0=1 at hd
    rw [hc] at hd
    linear_combination hd+2*n*c*hr⟩

theorem halfTranslationConjugate_label (n : ℤ) (a : SL(2,ℤ)) (c r : ℤ)
    (hc : a 1 0=4*c) (hr : a 1 1-a 0 0=2*r) :
    translationLabel ((n:ℚ)/2)*integralLabel a=
      integralLabel (halfTranslationConjugate n a c r hc hr)*translationLabel ((n:ℚ)/2) := by
  have hcr : (a 1 0:ℚ)=4*c := by exact_mod_cast hc
  have hrr : (a 1 1:ℚ)-(a 0 0:ℚ)=2*r := by exact_mod_cast hr
  apply Subtype.ext
  apply Subtype.ext
  change rationalMap (AsymptoticMobiusFold.translation ((n:ℚ)/2))*rationalMap (rationalGL a)=
    rationalMap (rationalGL (halfTranslationConjugate n a c r hc hr))*
      rationalMap (AsymptoticMobiusFold.translation ((n:ℚ)/2))
  rw [←map_mul,←map_mul]
  congr 1
  apply Units.ext
  change (AsymptoticMobiusFold.translation ((n:ℚ)/2)).val*(rationalGL a).val=
    (rationalGL (halfTranslationConjugate n a c r hc hr)).val*
      (AsymptoticMobiusFold.translation ((n:ℚ)/2)).val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AsymptoticMobiusFold.translation,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two,rationalGL_apply,halfTranslationConjugate,hcr]
  all_goals first | (solve | ring) | linear_combination (n:ℚ)/2*hrr

/-- Every half-integral translation normalizes Gamma0(N) when 4 divides N. -/
theorem halfTranslation_conj_mem (N : ℕ) (hN : 4∣N) (n : ℤ)
    {b : AsymptoticRationalGroup.Group} (hb : b∈gamma N) :
    translationLabel ((n:ℚ)/2)*b*(translationLabel ((n:ℚ)/2))⁻¹∈gamma N := by
  obtain ⟨a,ha,rfl⟩ := hb
  have hd : (4:ℤ)∣a 1 0 := (by exact_mod_cast hN : (4:ℤ)∣(N:ℤ)).trans
    ((gamma0_mem_dvd N a).mp ha)
  obtain ⟨c,hc⟩ := hd
  obtain ⟨r,hr⟩ := halfTranslation_diagonal_difference a c hc
  rw [halfTranslationConjugate_label n a c r hc hr,mul_inv_cancel_right]
  refine ⟨halfTranslationConjugate n a c r hc hr,?_,rfl⟩
  apply (gamma0_mem_dvd N _).mpr
  change (N:ℤ)∣4*c
  rw [←hc]
  exact (gamma0_mem_dvd N a).mp ha

theorem halfTranslation_inv_conj_mem (N : ℕ) (hN : 4∣N) (n : ℤ)
    {b : AsymptoticRationalGroup.Group} (hb : b∈gamma N) :
    (translationLabel ((n:ℚ)/2))⁻¹*b*translationLabel ((n:ℚ)/2)∈gamma N := by
  have h := halfTranslation_conj_mem N hN (-n) hb
  simpa only [Int.cast_neg,neg_div,translationLabel_inv,neg_neg] using h

#print axioms halfTranslation_diagonal_difference
#print axioms halfTranslationConjugate_label
#print axioms halfTranslation_conj_mem
#print axioms halfTranslation_inv_conj_mem

end QuantitativeMaass
