module

public import AsymptoticClassicalHeckeAverageV1
public import AsymptoticClassicalTranslateEquivV1
public import AsymptoticClassicalTriangularSlashV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane Matrix ConjAct AsymptoticCongruenceLabels
open AsymptoticClassicalDiscriminant
open scoped ModularForm MatrixGroups Pointwise

/-- The rational matrix giving the standard downward Hecke direction. -/
def upperDilationGL (p : ℕ) (hp : 0 < p) : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, (p : ℚ)] (by
    simpa [Matrix.det_fin_two] using (show (p : ℚ) ≠ 0 by exact_mod_cast hp.ne'))

def upperDilationReal (p : ℕ) (hp : 0 < p) : GL (Fin 2) ℝ :=
  (upperDilationGL p hp).map (Rat.castHom ℝ)

theorem upperDilationReal_eq (p : ℕ) (hp : 0 < p) :
    upperDilationReal p hp = triangularGL 1 0 p (by norm_num) (by exact_mod_cast hp) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperDilationReal, upperDilationGL, triangularGL, GeneralLinearGroup.map,
      GeneralLinearGroup.mkOfDetNeZero]

theorem upperDilationReal_det (p : ℕ) (hp : 0 < p) :
    (upperDilationReal p hp).det.val = (p : ℝ) := by
  rw [upperDilationReal_eq, triangularGL_det, one_mul]

/-- The source group for the standard U_p trace correspondence. -/
def upperDilationLevel (N p : ℕ) (hp : 0 < p) : Subgroup (GL (Fin 2) ℝ) :=
  toConjAct (upperDilationReal p hp)⁻¹ • level N

instance upperDilationLevel_det (N p : ℕ) (hp : 0 < p) :
    (upperDilationLevel N p hp).HasDetOne := inferInstanceAs
      (toConjAct (upperDilationReal p hp)⁻¹ • level N).HasDetOne

instance upperDilationLevel_arithmetic (N p : ℕ) (hp : 0 < p) [NeZero N] :
    (upperDilationLevel N p hp).IsArithmetic := by
  change (toConjAct (upperDilationReal p hp)⁻¹ • level N).IsArithmetic
  have he : (upperDilationReal p hp)⁻¹ =
      GeneralLinearGroup.map (Rat.castHom ℝ) (upperDilationGL p hp)⁻¹ :=
    (map_inv (GeneralLinearGroup.map (Rat.castHom ℝ)) _).symm
  rw [he]
  exact Subgroup.IsArithmetic.conj (level N) _

/-- Integral matrices whose upper-right entry is divisible by p. -/
def upperCongruence (p : ℕ) : Subgroup SL(2, ℤ) where
  carrier := {A | (p : ℤ) ∣ A 0 1}
  one_mem' := by simp
  mul_mem' := by
    intro A B hA hB
    change (p : ℤ) ∣ (A.val * B.val) 0 1
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    exact dvd_add (dvd_mul_of_dvd_right hB _) (dvd_mul_of_dvd_left hA _)
  inv_mem' := by
    intro A hA
    simpa [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two] using dvd_neg.mpr hA

/-- Clearing the upper-right denominator in conjugation by diag(1,p). -/
def upperDilationConjugate (p : ℕ) (A : SL(2, ℤ)) (b : ℤ)
    (hb : A 0 1 = (p : ℤ) * b) : SL(2, ℤ) :=
  ⟨!![A 0 0, b; (p : ℤ) * A 1 0, A 1 1], by
    have hd := A.property
    rw [Matrix.det_fin_two] at hd ⊢
    change A 0 0 * A 1 1 - b * ((p : ℤ) * A 1 0) = 1
    rw [hb] at hd
    nlinarith [hd]⟩

theorem upperDilationConjugate_mem (N p : ℕ) (A : SL(2, ℤ))
    (hA : A ∈ CongruenceSubgroup.Gamma0 N) (b : ℤ) (hb : A 0 1 = (p : ℤ) * b) :
    upperDilationConjugate p A b hb ∈ CongruenceSubgroup.Gamma0 N := by
  rw [gamma0_mem_dvd] at hA ⊢
  exact dvd_mul_of_dvd_right hA _

theorem upperDilation_intertwine (p : ℕ) (hp : 0 < p) (A : SL(2, ℤ))
    (b : ℤ) (hb : A 0 1 = (p : ℤ) * b) :
    upperDilationReal p hp * SpecialLinearGroup.mapGL ℝ A =
      SpecialLinearGroup.mapGL ℝ (upperDilationConjugate p A b hb) *
        upperDilationReal p hp := by
  apply Units.ext
  change (upperDilationReal p hp).val * A.val.map (fun z : ℤ => (z : ℝ)) =
    (upperDilationConjugate p A b hb).val.map (fun z : ℤ => (z : ℝ)) *
      (upperDilationReal p hp).val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperDilationReal, upperDilationGL, GeneralLinearGroup.map,
      GeneralLinearGroup.mkOfDetNeZero, upperDilationConjugate, Matrix.mul_apply,
      Fin.sum_univ_two, hb]
  all_goals ring

theorem upperDilationLevel_mem_iff (N p : ℕ) (hp : 0 < p) (A : SL(2, ℤ))
    (hA : A ∈ CongruenceSubgroup.Gamma0 N) :
    SpecialLinearGroup.mapGL ℝ A ∈ upperDilationLevel N p hp ↔ (p : ℤ) ∣ A 0 1 := by
  constructor
  · rintro ⟨_, ⟨B, hB, rfl⟩, he⟩
    have hi : upperDilationReal p hp * SpecialLinearGroup.mapGL ℝ A =
        SpecialLinearGroup.mapGL ℝ B * upperDilationReal p hp := by
      rw [← he]
      change upperDilationReal p hp * ((upperDilationReal p hp)⁻¹ *
        SpecialLinearGroup.mapGL ℝ B * ((upperDilationReal p hp)⁻¹)⁻¹) = _
      group
    have hb := congrArg (fun g : GL (Fin 2) ℝ => g.val 0 1) hi
    have hb' : (A 0 1 : ℝ) = (p : ℝ) * (B 0 1 : ℝ) := by
      simpa [upperDilationReal, upperDilationGL, GeneralLinearGroup.map,
        GeneralLinearGroup.mkOfDetNeZero, SpecialLinearGroup.mapGL,
        Matrix.mul_apply, Fin.sum_univ_two, mul_comm] using hb
    exact ⟨B 0 1, by exact_mod_cast hb'⟩
  · rintro ⟨b, hb⟩
    refine ⟨SpecialLinearGroup.mapGL ℝ (upperDilationConjugate p A b hb),
      ⟨_, upperDilationConjugate_mem N p A hA b hb, rfl⟩, ?_⟩
    change (upperDilationReal p hp)⁻¹ * _ * ((upperDilationReal p hp)⁻¹)⁻¹ = _
    rw [inv_inv, mul_assoc, ← upperDilation_intertwine p hp A b hb, inv_mul_cancel_left]

#print axioms upperDilationLevel_mem_iff
#print axioms upperDilationReal_eq
#print axioms upperDilationReal_det
#print axioms upperDilationLevel_arithmetic
#print axioms upperDilationConjugate_mem
#print axioms upperDilation_intertwine

end AsymptoticClassicalCusp
