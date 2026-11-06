module

public import AsymptoticSlashGaugeV1
public import AsymptoticFoldedLowV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRationalBranches

open UpperHalfPlane AsymptoticRationalGroup AsymptoticRationalFreeness
open AsymptoticReconstructionBranch

/-- The actual positive projective label of a rational matrix. -/
noncomputable def ofMatrix (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val) :
    AsymptoticRationalGroup.Group :=
  ⟨⟨rationalMap g,⟨g,rfl⟩⟩,by
    apply Units.ext
    change SignType.sign (realMatrix g).det.val=1
    exact sign_eq_one_iff.mpr hg⟩

theorem ofMatrix_action (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val) (z : ℍ) :
    ofMatrix g hg • z=realMatrix g • z := by
  change rationalMap g • z=realMatrix g • z
  exact pglMk_smul _ _

theorem action_continuous (g : AsymptoticRationalGroup.Group) :
    Continuous (fun z : ℍ => g • z) := by
  have he : (fun z : ℍ => g • z)=fun z => realMatrix (AsymptoticSlashGauge.representative g) • z :=
    funext (fun z => (AsymptoticSlashGauge.representative_action g z).symm)
  rw [he]
  exact continuous_const_smul _

theorem realMatrix_branch (L b d : ℚ) (hL : L≠0) :
    realMatrix (branch L b d hL)=branch (L:ℝ) (b:ℝ) (d:ℝ) (by exact_mod_cast hL) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realMatrix,branch,Matrix.GeneralLinearGroup.map,Matrix.GeneralLinearGroup.mkOfDetNeZero]

noncomputable def fold {L : ℚ} (hL : 0<L) (b d : ℚ) (n : ℤ) : AsymptoticRationalGroup.Group :=
  ofMatrix (branch L b (d-n) hL.ne') (by
    rw [realMatrix_branch,branch_det]
    exact_mod_cast hL)

theorem fold_action {L : ℚ} (hL : 0<L) (b d : ℚ) (n : ℤ) (z : ℍ) :
    fold hL b d n • z=
      AsymptoticFoldedLow.fold (show (0:ℝ)<L by exact_mod_cast hL) (b:ℝ) (d:ℝ) n • z := by
  rw [fold,ofMatrix_action,realMatrix_branch]
  simp only [Rat.cast_sub,Rat.cast_intCast,AsymptoticFoldedLow.fold]

#print axioms ofMatrix_action
#print axioms realMatrix_branch
#print axioms fold_action

end AsymptoticRationalBranches
