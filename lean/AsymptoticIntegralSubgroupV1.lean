module

public import AsymptoticRationalCompactFoldV1
public import Mathlib.NumberTheory.Padics.PadicNorm

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticIntegralSubgroup

open Matrix AsymptoticRationalGroup AsymptoticRationalBranches AsymptoticRationalFreeness
open AsymptoticMobiusFold
open scoped MatrixGroups

variable (q : ℕ) [Fact q.Prime]

/-- Entrywise integrality at q, expressed using the rational q-adic norm. -/
def IntegralEntries (A : Matrix (Fin 2) (Fin 2) ℚ) : Prop :=
  ∀ i j,padicNorm q (A i j)≤1

omit [Fact q.Prime] in
theorem integralEntries_one : IntegralEntries q 1 := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.one_apply]

theorem integralEntries_mul (A B : Matrix (Fin 2) (Fin 2) ℚ)
    (hA : IntegralEntries q A) (hB : IntegralEntries q B) : IntegralEntries q (A*B) := by
  intro i j
  rw [Matrix.mul_apply]
  apply padicNorm.sum_le' _ (by norm_num)
  intro k hk
  rw [padicNorm.mul]
  exact (mul_le_mul_of_nonneg_right (hA i k) (padicNorm.nonneg _)).trans (by simpa only [one_mul] using hB k j)

/-- Rational matrices integral with integral inverse. Passing to PGL
allows every projectively equivalent integral representative. -/
def integralGL : Subgroup (GL (Fin 2) ℚ) where
  carrier := {g | IntegralEntries q g.val ∧ IntegralEntries q g⁻¹.val}
  one_mem' := ⟨integralEntries_one q,by simpa only [inv_one,Units.val_one] using integralEntries_one q⟩
  mul_mem' := by
    intro g h hg hh
    exact ⟨integralEntries_mul q _ _ hg.1 hh.1,
      by simpa only [_root_.mul_inv_rev,Units.val_mul] using integralEntries_mul q _ _ hh.2 hg.2⟩
  inv_mem' := by
    intro g hg
    exact ⟨hg.2,by simpa only [inv_inv] using hg.1⟩

/-- The q-integral subgroup of the actual positive rational projective
group used by the regular representation. -/
noncomputable def integralGroup : Subgroup AsymptoticRationalGroup.Group :=
  ((integralGL q).map rationalMap).comap
    (rationalImage.subtype.comp rationalSign.ker.subtype)

theorem ofMatrix_mem (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    (hi : g∈integralGL q) : ofMatrix g hg∈integralGroup q :=
  ⟨g,hi,rfl⟩

theorem integralGroup_mem_iff (g : AsymptoticRationalGroup.Group) :
    g∈integralGroup q ↔ ∃ A : GL (Fin 2) ℚ,A∈integralGL q ∧ rationalMap A=g.val.val := Iff.rfl

omit [Fact q.Prime] in
theorem translation_inv (r : ℚ) : (translation r)⁻¹=translation (-r) := by
  apply inv_eq_of_mul_eq_one_left
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [translation,Matrix.GeneralLinearGroup.mkOfDetNeZero,Matrix.mul_apply,Fin.sum_univ_two]

theorem translation_integral_iff (r : ℚ) : translation r∈integralGL q ↔ padicNorm q r≤1 := by
  constructor
  · intro h
    exact h.1 0 1
  · intro h
    constructor
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [translation,Matrix.GeneralLinearGroup.mkOfDetNeZero,h]
    · rw [translation_inv]
      intro i j
      fin_cases i <;> fin_cases j <;> simp [translation,Matrix.GeneralLinearGroup.mkOfDetNeZero,h]

theorem translation_fraction_integral (a : ℤ) (b : ℕ) (hb : ¬q∣b) :
    translation ((a:ℚ)/b)∈integralGL q := by
  rw [translation_integral_iff,padicNorm.div,(padicNorm.nat_eq_one_iff b).mpr hb,div_one]
  exact padicNorm.of_int a

theorem translation_integer_integral (a : ℤ) : translation (a:ℚ)∈integralGL q :=
  (translation_integral_iff q a).mpr (padicNorm.of_int a)

#print axioms integralEntries_one
#print axioms integralEntries_mul
#print axioms ofMatrix_mem
#print axioms integralGroup_mem_iff
#print axioms translation_inv
#print axioms translation_integral_iff
#print axioms translation_fraction_integral
#print axioms translation_integer_integral

end AsymptoticIntegralSubgroup
