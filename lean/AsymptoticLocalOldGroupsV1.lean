module

public import AsymptoticPrimeSeparatedGroupsV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public section

namespace AsymptoticLocalCongruence

open Matrix AsymptoticCongruenceLabels AsymptoticCongruenceStrip AsymptoticIntegralSubgroup
open AsymptoticRationalGroup AsymptoticRationalFreeness
open scoped MatrixGroups

theorem lower_integral_mem_outside (M p : ℕ) (hM : 0<M) (hp : p.Prime)
    (A : SL(2,ℤ)) (hA : A∈CongruenceSubgroup.Gamma0 M) :
    SpecialLinearGroup.map (Int.castRingHom ℚ) A∈outside (p*M) {p} := by
  rw [mem_outside]
  intro q hq hqp
  let : Fact q.Prime := ⟨hq⟩
  have hqp' : ¬q∣p := fun h => hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp h)
  have hm := (mem_outside M ∅ _).mp (integral_mem_outside M hM ∅ A hA) q hq (Set.notMem_empty q)
  refine ⟨hm.1,?_⟩
  change padicNorm q ((A.val 1 0:ℚ)/(p*M:ℕ))≤1
  have he : (A.val 1 0:ℚ)/(p*M:ℕ)=((A.val 1 0:ℚ)/(M:ℚ))/(p:ℚ) := by
    push_cast
    ring
  rw [he,padicNorm.div,(padicNorm.nat_eq_one_iff p).mpr hqp',div_one]
  exact hm.2

/-- The first old group is supported at its one ramified prime. -/
theorem gamma_lower_le_projectiveOutside (M p : ℕ) (hM : 0<M) (hp : p.Prime) :
    gamma M ≤ projectiveOutside (p*M) {p} := by
  rintro g ⟨A,hA,rfl⟩
  exact ⟨SpecialLinearGroup.map (Int.castRingHom ℚ) A,
    lower_integral_mem_outside M p hM hp A hA,rationalSLLabel_integral A⟩

/-- Conjugation by D_p, expressed as a rational special-linear matrix. -/
def dilationConjugateSL (p : ℕ) (hp : 0<p) (A : SL(2,ℤ)) : SL(2,ℚ) :=
  ⟨!![(A.val 0 0:ℚ),(A.val 0 1:ℚ)/p;(p:ℚ)*A.val 1 0,(A.val 1 1:ℚ)],by
    have hp' : (p:ℚ)≠0 := by exact_mod_cast hp.ne'
    have hdZ := A.property
    rw [Matrix.det_fin_two] at hdZ
    have hd : (A.val 0 0:ℚ)*(A.val 1 1:ℚ)-(A.val 0 1:ℚ)*(A.val 1 0:ℚ)=1 := by
      exact_mod_cast hdZ
    rw [Matrix.det_fin_two]
    change (A.val 0 0:ℚ)*(A.val 1 1:ℚ)-((A.val 0 1:ℚ)/p)*((p:ℚ)*(A.val 1 0:ℚ))=1
    rw [← mul_assoc,div_mul_cancel₀ _ hp']
    exact hd⟩

theorem dilationConjugateSL_label (p : ℕ) (hp : 0<p) (A : SL(2,ℤ)) :
    rationalSLLabel (dilationConjugateSL p hp A)=
      (dilationLabel p hp)⁻¹*integralLabel A*dilationLabel p hp := by
  have hp' : (p:ℚ)≠0 := by exact_mod_cast hp.ne'
  apply (mul_left_cancel (a:=dilationLabel p hp))
  simp only [← mul_assoc,mul_inv_cancel,one_mul]
  apply Subtype.ext
  apply Subtype.ext
  change rationalMap (dilationGL p hp)*rationalMap (SpecialLinearGroup.toGL (dilationConjugateSL p hp A))=
    rationalMap (rationalGL A)*rationalMap (dilationGL p hp)
  rw [←map_mul,←map_mul]
  congr 1
  apply Units.ext
  change (dilationGL p hp).val*(dilationConjugateSL p hp A).val=
    A.val.map (fun z : ℤ => (z:ℚ))*(dilationGL p hp).val
  ext i j
  simp only [Matrix.mul_apply,Fin.sum_univ_two,Matrix.map_apply]
  fin_cases i <;> fin_cases j <;>
    simp [dilationGL,dilationConjugateSL,GeneralLinearGroup.mkOfDetNeZero,mul_comm]
  exact mul_div_cancel₀ (A.val 0 1:ℚ) hp'

theorem dilationConjugateSL_mem_outside (M p : ℕ) (hM : 0<M) (hp : p.Prime)
    (A : SL(2,ℤ)) (hA : A∈CongruenceSubgroup.Gamma0 M) :
    dilationConjugateSL p hp.pos A∈outside (p*M) {p} := by
  rw [mem_outside]
  intro q hq hqp
  let : Fact q.Prime := ⟨hq⟩
  have hqp' : ¬q∣p := fun h => hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp h)
  have hn : padicNorm q (p:ℚ)=1 := (padicNorm.nat_eq_one_iff p).mpr hqp'
  constructor
  · intro i j
    fin_cases i <;> fin_cases j
    · exact padicNorm.of_int (A.val 0 0)
    · change padicNorm q ((A.val 0 1:ℚ)/p)≤1
      rw [padicNorm.div,hn,div_one]
      exact padicNorm.of_int _
    · change padicNorm q ((p:ℚ)*(A.val 1 0:ℚ))≤1
      rw [padicNorm.mul,hn,one_mul]
      exact padicNorm.of_int _
    · exact padicNorm.of_int (A.val 1 1)
  · have hm := (mem_outside M ∅ _).mp (integral_mem_outside M hM ∅ A hA) q hq (Set.notMem_empty q)
    change padicNorm q (((p:ℚ)*(A.val 1 0:ℚ))/(p*M:ℕ))≤1
    have he : ((p:ℚ)*(A.val 1 0:ℚ))/(p*M:ℕ)=(A.val 1 0:ℚ)/(M:ℚ) := by
      have hp' : (p:ℚ)≠0 := by exact_mod_cast hp.ne_zero
      push_cast
      field_simp
    rw [he]
    exact hm.2

/-- The second old group has the same one-prime support. -/
theorem degeneracy_le_projectiveOutside (M p : ℕ) (hM : 0<M) (hp : p.Prime) :
    degeneracyGroup M p hp.pos ≤ projectiveOutside (p*M) {p} := by
  rintro g ⟨a,⟨A,hA,rfl⟩,rfl⟩
  refine ⟨dilationConjugateSL p hp.pos A,dilationConjugateSL_mem_outside M p hM hp A hA,?_⟩
  change rationalSLLabel (dilationConjugateSL p hp.pos A)=
    (dilationLabel p hp.pos)⁻¹*integralLabel A*((dilationLabel p hp.pos)⁻¹)⁻¹
  rw [inv_inv]
  exact dilationConjugateSL_label p hp.pos A

#print axioms lower_integral_mem_outside
#print axioms gamma_lower_le_projectiveOutside
#print axioms dilationConjugateSL_label
#print axioms dilationConjugateSL_mem_outside
#print axioms degeneracy_le_projectiveOutside

end AsymptoticLocalCongruence
