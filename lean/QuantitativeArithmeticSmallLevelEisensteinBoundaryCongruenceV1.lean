module

public import QuantitativeArithmeticSmallLevelEisensteinBoundaryTransportV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelEisenstein

open Matrix UpperHalfPlane Filter AsymptoticClassicalDiscriminant
open scoped MatrixGroups ModularForm

def boundaryTranslation (t : ℤ) : SL(2,ℤ) := ⟨!![1,t;0,1], by simp⟩

theorem boundaryTranslation_real (t : ℤ) :
    SpecialLinearGroup.mapGL ℝ (boundaryTranslation t) =
      triangularGL 1 (t : ℝ) 1 (by norm_num) (by norm_num) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boundaryTranslation,triangularGL,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.mapGL,SpecialLinearGroup.map]

variable (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic] [Γ.HasDetOne] (k : ℤ)

theorem cuspBoundary_right_translation (F : ModularForm Γ k) (γ : SL(2,ℤ)) (t : ℤ) :
    cuspBoundary Γ k F (γ * boundaryTranslation t) = cuspBoundary Γ k F γ := by
  rw [cuspBoundary_apply,SlashAction.slash_mul,ModularForm.SL_slash]
  have ht := boundaryTranslation_real t
  change SpecialLinearGroup.toGL (SpecialLinearGroup.map (Int.castRingHom ℝ)
    (boundaryTranslation t)) = triangularGL 1 (t : ℝ) 1 (by norm_num) (by norm_num) at ht
  rw [ht]
  have h := cuspBoundary_triangular Γ k F γ 1 (t : ℝ) 1 (by norm_num) (by norm_num)
  simpa [triangularFactor] using h

/-- Congruent primitive first columns give the same cusp constant whenever
Γ contains the principal level-N subgroup. This works for arbitrary N,
without selecting a list of cusps or assuming an Eisenstein classification. -/
theorem cuspBoundary_column_congr (N : ℕ)
    (hΓ : ∀ rho ∈ CongruenceSubgroup.Gamma N, SpecialLinearGroup.mapGL ℝ rho ∈ Γ)
    (F : ModularForm Γ k) (γ δ : SL(2,ℤ))
    (hcol : ∀ i : Fin 2, (γ i 0 : ZMod N) = (δ i 0 : ZMod N)) :
    cuspBoundary Γ k F γ = cuspBoundary Γ k F δ := by
  let A := δ⁻¹ * γ
  have hAcol : ∀ i : Fin 2, (A i 0 : ZMod N) = if i=0 then 1 else 0 := by
    intro i
    have hmul : (δ⁻¹).val * δ.val = (1 : Matrix (Fin 2) (Fin 2) ℤ) :=
      congrArg (fun u : SL(2,ℤ) ↦ u.val) (inv_mul_cancel δ)
    have hm := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℤ ↦ (B i 0 : ZMod N)) hmul
    change (((δ⁻¹).val * γ.val) i 0 : ZMod N) = _
    simp only [Matrix.mul_apply,Fin.sum_univ_two,Int.cast_add,Int.cast_mul,hcol 0,hcol 1]
    simpa only [Matrix.mul_apply,Fin.sum_univ_two,Int.cast_add,Int.cast_mul,
      Matrix.one_apply,Int.cast_ite,Int.cast_one,Int.cast_zero] using hm
  have hA00 : (A 0 0 : ZMod N) = 1 := by simpa using hAcol 0
  have hA10 : (A 1 0 : ZMod N) = 0 := by simpa using hAcol 1
  have hA11 : (A 1 1 : ZMod N) = 1 := by
    have hd := congrArg (Int.castRingHom (ZMod N)) A.property
    rw [Matrix.det_fin_two] at hd
    simpa [hA00,hA10] using hd
  let t : ℤ := A 0 1
  let red : SL(2,ℤ) →* SL(2,ZMod N) := SpecialLinearGroup.map (Int.castRingHom (ZMod N))
  have hA : red A = red (boundaryTranslation t) := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [red,SpecialLinearGroup.map,boundaryTranslation,t,hA00,hA10,hA11]
  have hγ : red γ = red δ * red (boundaryTranslation t) := by
    rw [← hA,← map_mul]
    simp [A]
  let rho := γ * (boundaryTranslation t)⁻¹ * δ⁻¹
  have hrho : rho ∈ CongruenceSubgroup.Gamma N := by
    apply CongruenceSubgroup.Gamma_mem'.mpr
    change red rho = 1
    simp only [rho,map_mul,map_inv,hγ]
    group
  have he : γ = rho * (δ * boundaryTranslation t) := by
    dsimp [rho]
    group
  rw [he,cuspBoundary_left Γ k F rho _ (hΓ rho hrho),cuspBoundary_right_translation]

#print axioms cuspBoundary_right_translation
#print axioms cuspBoundary_column_congr

end QuantitativeArithmeticSmallLevelEisenstein
