module

public import AsymptoticIntegralSubgroupV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticIntegralSubgroup

open Matrix AsymptoticRationalGroup AsymptoticRationalBranches AsymptoticRationalFreeness
open AsymptoticMobiusFold
open scoped MatrixGroups

variable (q : ℕ) [Fact q.Prime]

/-- Scalar changes of representative cannot make a nonintegral
translation integral. The diagonal entries of a representative and its
inverse force its scalar factor to have q-adic norm one. -/
theorem projective_translation_integral (g : GL (Fin 2) ℚ) (hg : g∈integralGL q)
    (r : ℚ) (he : rationalMap g=rationalMap (translation r)) : padicNorm q r≤1 := by
  change ProjGenLinGroup.mk (realMatrix g)=ProjGenLinGroup.mk (realMatrix (translation r)) at he
  obtain ⟨u,hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp he.symm
  have h00 := congrArg (fun A : GL (Fin 2) ℝ => A.val 0 0) hu
  have h10 := congrArg (fun A : GL (Fin 2) ℝ => A.val 1 0) hu
  have h01 := congrArg (fun A : GL (Fin 2) ℝ => A.val 0 1) hu
  have hu0 : (u:ℝ)=(g.val 0 0:ℝ) := by
    simpa [realMatrix,translation,GeneralLinearGroup.map,GeneralLinearGroup.mkOfDetNeZero,
      GeneralLinearGroup.scalar,Matrix.mul_apply,Fin.sum_univ_two,Matrix.scalar,Matrix.diagonal] using h00
  have hg10 : g.val 1 0=0 := by
    have hh : (0:ℝ)=(g.val 1 0:ℝ) := by
      simpa [realMatrix,translation,GeneralLinearGroup.map,GeneralLinearGroup.mkOfDetNeZero,
        GeneralLinearGroup.scalar,Matrix.mul_apply,Fin.sum_univ_two,Matrix.scalar,Matrix.diagonal] using h10
    exact_mod_cast hh.symm
  have hg01 : g.val 0 1=r*g.val 0 0 := by
    have hh : (r:ℝ)*(u:ℝ)=(g.val 0 1:ℝ) := by
      simpa [realMatrix,translation,GeneralLinearGroup.map,GeneralLinearGroup.mkOfDetNeZero,
        GeneralLinearGroup.scalar,Matrix.mul_apply,Fin.sum_univ_two,Matrix.scalar,Matrix.diagonal] using h01
    rw [hu0] at hh
    exact_mod_cast hh.symm
  have hi : (g⁻¹).val 0 0*g.val 0 0=1 := by
    have hh := congrArg (fun A : GL (Fin 2) ℚ => A.val 0 0) (inv_mul_cancel g)
    change ((g⁻¹).val*g.val) 0 0=1 at hh
    simpa only [Matrix.mul_apply,Fin.sum_univ_two,hg10,mul_zero,add_zero] using hh
  have hn := congrArg (padicNorm q) hi
  rw [padicNorm.mul,padicNorm.one] at hn
  have hn0 : padicNorm q (g.val 0 0)=1 := by
    apply le_antisymm (hg.1 0 0)
    have hb := mul_le_mul_of_nonneg_right (hg.2 0 0) (padicNorm.nonneg (p:=q) (g.val 0 0))
    simpa only [hn,one_mul] using hb
  have hb := hg.1 0 1
  rwa [hg01,padicNorm.mul,hn0,mul_one] at hb

noncomputable def translationLabel (r : ℚ) : AsymptoticRationalGroup.Group :=
  ofMatrix (translation r) (by rw [realMatrix_translation,translation_det]; norm_num)

theorem translationLabel_mem_iff (r : ℚ) :
    translationLabel r∈integralGroup q ↔ padicNorm q r≤1 := by
  constructor
  · intro h
    obtain ⟨g,hg,he⟩ := (integralGroup_mem_iff q (translationLabel r)).mp h
    exact projective_translation_integral q g hg r he
  · intro h
    exact ofMatrix_mem q _ _ ((translation_integral_iff q r).mpr h)

theorem translationLabel_integer_mem (b : ℤ) : translationLabel (b:ℚ)∈integralGroup q :=
  (translationLabel_mem_iff q b).mpr (padicNorm.of_int b)

/-- A translation by b/q with b prime to q is outside the projective
q-integral subgroup, regardless of scalar representative. -/
theorem translationLabel_fraction_not_mem (b : ℤ) (hb : ¬(q:ℤ)∣b) :
    translationLabel ((b:ℚ)/q)∉integralGroup q := by
  rw [translationLabel_mem_iff,padicNorm.div,(padicNorm.int_eq_one_iff b).mpr hb,
    padicNorm.padicNorm_p_of_prime,one_div,inv_inv]
  exact not_le_of_gt (by exact_mod_cast (Fact.out : q.Prime).one_lt)

#print axioms projective_translation_integral
#print axioms translationLabel_mem_iff
#print axioms translationLabel_integer_mem
#print axioms translationLabel_fraction_not_mem

end AsymptoticIntegralSubgroup
