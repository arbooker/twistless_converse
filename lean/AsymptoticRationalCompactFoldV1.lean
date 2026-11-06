module

public import AsymptoticRationalBranchesV1
public import AsymptoticCompactBranchV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRationalBranches

open UpperHalfPlane AsymptoticRationalFreeness AsymptoticMobiusFold

theorem realMatrix_translation (r : ℚ) :
    realMatrix (translation r)=translation (r:ℝ) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realMatrix,translation,Matrix.GeneralLinearGroup.map,Matrix.GeneralLinearGroup.mkOfDetNeZero]

noncomputable def foldMatrix (g : GL (Fin 2) ℚ) (n : ℤ) : GL (Fin 2) ℚ :=
  translation (-(n:ℚ))*g

theorem realMatrix_foldMatrix (g : GL (Fin 2) ℚ) (n : ℤ) :
    realMatrix (foldMatrix g n)=AsymptoticMobiusFold.fold (realMatrix g) n := by
  change (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ)) (translation (-(n:ℚ))*g)=_
  rw [map_mul]
  change realMatrix (translation (-(n:ℚ)))*realMatrix g=_
  rw [realMatrix_translation]
  simp only [Rat.cast_neg,Rat.cast_intCast,AsymptoticMobiusFold.fold]

theorem foldMatrix_positive (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val) (n : ℤ) :
    0<(realMatrix (foldMatrix g n)).det.val := by
  rw [realMatrix_foldMatrix,AsymptoticMobiusFold.fold,map_mul,Units.val_mul,translation_det,one_mul]
  exact hg

noncomputable def compactFold (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val) (n : ℤ) :
    AsymptoticRationalGroup.Group := ofMatrix (foldMatrix g n) (foldMatrix_positive g hg n)

theorem compactFold_action (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val) (n : ℤ) (z : ℍ) :
    compactFold g hg n • z=AsymptoticMobiusFold.fold (realMatrix g) n • z := by
  rw [compactFold,ofMatrix_action,realMatrix_foldMatrix]

#print axioms realMatrix_translation
#print axioms realMatrix_foldMatrix
#print axioms compactFold_action

end AsymptoticRationalBranches
