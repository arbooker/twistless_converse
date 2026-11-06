module

public import AsymptoticClassicalDiscriminantLevelV1
public import AsymptoticClassicalDilationTriangularV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace AsymptoticClassicalDiscriminant

open UpperHalfPlane Matrix AsymptoticClassicalCusp AsymptoticCongruenceLabels
open scoped ModularForm MatrixGroups

variable (N : ℕ) (hN : 0 < N)

theorem atLevel_eq_scaled_slash :
    (atLevel N hN : ℍ → ℂ) = (N : ℂ) ^ (-11 : ℤ) •
      ((ModularForm.discriminant : ℍ → ℂ) ∣[(12 : ℤ)] dilationReal N hN) := by
  funext z
  exact (degeneracyForm_apply 1 N hN 12
    (restrict 12 (level_le_SL 1) CuspForm.discriminant) z).symm

/-- A slash stabilizer of Delta(N*z) must satisfy the exact Gamma0(N)
 congruence condition. The proof compares the positive triangular slopes. -/
theorem stabilizer_mem (A : SL(2, ℤ))
    (hA : (atLevel N hN : ℍ → ℂ) ∣[(12 : ℤ)] A = atLevel N hN) :
    A ∈ CongruenceSubgroup.Gamma0 N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [atLevel_eq_scaled_slash, ModularForm.SL_smul_slash] at hA
  have hslash : (ModularForm.discriminant : ℍ → ℂ) ∣[(12 : ℤ)]
      (dilationReal N hN * SpecialLinearGroup.mapGL ℝ A) =
      (ModularForm.discriminant : ℍ → ℂ) ∣[(12 : ℤ)] dilationReal N hN := by
    funext z
    have hh := congrFun hA z
    change (N : ℂ) ^ (-11 : ℤ) *
      (((ModularForm.discriminant : ℍ → ℂ) ∣[(12 : ℤ)] dilationReal N hN)
        ∣[(12 : ℤ)] SpecialLinearGroup.mapGL ℝ A) z =
      (N : ℂ) ^ (-11 : ℤ) *
        ((ModularForm.discriminant : ℍ → ℂ) ∣[(12 : ℤ)] dilationReal N hN) z at hh
    simpa only [SlashAction.slash_mul] using mul_left_cancel₀ (zpow_ne_zero _ hNC) hh
  obtain ⟨U, a, b, d, ha, hd, had, hc, heD⟩ := dilation_triangular N hN A
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hu : (ModularForm.discriminant : ℍ → ℂ) ∣[(12 : ℤ)]
      SpecialLinearGroup.mapGL ℝ U = ModularForm.discriminant :=
    CuspForm.discriminant.slash_action_eq' _ ⟨U, rfl⟩
  have hD : dilationReal N hN = triangularGL (N : ℝ) 0 1 hNR (by norm_num) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dilationReal, dilationGL, GeneralLinearGroup.map, triangularGL,
        GeneralLinearGroup.mkOfDetNeZero]
  rw [heD, SlashAction.slash_mul, hu, hD] at hslash
  have hleft := triangularFactor_ne_zero (a : ℝ) (d : ℝ) haR hdR 12
  have hright := triangularFactor_ne_zero (N : ℝ) 1 hNR (by norm_num) 12
  let C : ℂ := (triangularFactor (a : ℝ) (d : ℝ) 12)⁻¹ * triangularFactor (N : ℝ) 1 12
  have hC : C ≠ 0 := mul_ne_zero (inv_ne_zero hleft) hright
  have he (z : ℍ) :
      ModularForm.discriminant (affine ((a : ℝ) / d) (div_pos haR hdR) ((b : ℝ) / d) z) =
        C * ModularForm.discriminant (affine (N : ℝ) hNR 0 z) := by
    have hh := congrFun hslash z
    rw [slash_triangular, slash_triangular] at hh
    simp only [div_one] at hh
    calc
      _ = (triangularFactor (a : ℝ) (d : ℝ) 12)⁻¹ *
          (triangularFactor (a : ℝ) (d : ℝ) 12 *
            ModularForm.discriminant (affine ((a : ℝ) / d) (div_pos haR hdR) ((b : ℝ) / d) z)) := by
        rw [← mul_assoc, inv_mul_cancel₀ hleft, one_mul]
      _ = _ := by rw [hh]; exact (mul_assoc _ _ _).symm
  have hratio := affine_slope_eq ((a : ℝ) / d) (N : ℝ) (div_pos haR hdR) hNR
    ((b : ℝ) / d) 0 C hC he
  have har : a = (N : ℤ) * d := by
    have hh := (div_eq_iff hdR.ne').mp hratio
    exact_mod_cast hh
  have hd1 : 1 ≤ d := by omega
  have hNI : (0 : ℤ) < N := by exact_mod_cast hN
  have haN : a = (N : ℤ) := by
    nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hd1),
      mul_nonneg hNI.le (sub_nonneg.mpr hd1)]
  rw [gamma0_mem_dvd]
  refine ⟨U 1 0, ?_⟩
  rw [hc, haN]
  ring

theorem stabilizer_iff (A : SL(2, ℤ)) :
    (atLevel N hN : ℍ → ℂ) ∣[(12 : ℤ)] A = atLevel N hN ↔
      A ∈ CongruenceSubgroup.Gamma0 N :=
  ⟨stabilizer_mem N hN A, atLevel_slash_eq N hN A⟩

#print axioms atLevel_eq_scaled_slash
#print axioms stabilizer_mem
#print axioms stabilizer_iff

end AsymptoticClassicalDiscriminant
