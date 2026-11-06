module

public import AsymptoticFrickeOldGroupV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticCongruenceLabels

open Matrix AsymptoticRationalGroup AsymptoticRationalFreeness AsymptoticRationalBranches
open AsymptoticFreshMatrices AsymptoticReconstructionBranch

/-- The usual degeneracy matrix D_p=diag(p,1), before passing to PGL. -/
def dilationGL (p : ℕ) (hp : 0<p) : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mkOfDetNeZero !![(p:ℚ),0;0,1] (by
    simp only [Matrix.det_fin_two]
    change (p:ℚ)*1-0*0≠0
    simpa using (show (p:ℚ)≠0 by exact_mod_cast hp.ne'))

theorem dilationGL_positive (p : ℕ) (hp : 0<p) : 0<(realMatrix (dilationGL p hp)).det.val := by
  change 0<((!![(p:ℚ),0;0,1]).map (algebraMap ℚ ℝ)).det
  rw [Matrix.det_fin_two]
  simpa using (show (0:ℝ)<p by exact_mod_cast hp)

noncomputable def dilationLabel (p : ℕ) (hp : 0<p) : AsymptoticRationalGroup.Group :=
  ofMatrix (dilationGL p hp) (dilationGL_positive p hp)

/-- The exact global Fricke/degeneracy identity. -/
theorem fricke_mul_dilation (M p : ℕ) (hM : 0<M) (hp : 0<p) :
    frickeLabel M hM*dilationLabel p hp=frickeLabel (p*M) (Nat.mul_pos hp hM) := by
  apply Subtype.ext
  apply Subtype.ext
  change rationalMap (branch (M:ℚ) 0 0 _)*rationalMap (dilationGL p hp)=
    rationalMap (branch ((p*M:ℕ):ℚ) 0 0 _)
  rw [← map_mul]
  congr 1
  apply Units.ext
  change (branch (M:ℚ) 0 0 _).val*(dilationGL p hp).val=(branch ((p*M:ℕ):ℚ) 0 0 _).val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [branch,dilationGL,GeneralLinearGroup.mkOfDetNeZero,Matrix.mul_apply,Fin.sum_univ_two,mul_comm]

theorem inv_dilation_mul_fricke (M p : ℕ) (hM : 0<M) (hp : 0<p) :
    (dilationLabel p hp)⁻¹*frickeLabel M hM=frickeLabel (p*M) (Nat.mul_pos hp hM) := by
  have he := congrArg Inv.inv (fricke_mul_dilation M p hM hp)
  simpa only [_root_.mul_inv_rev,frickeLabel_inv] using he

#print axioms dilationGL_positive
#print axioms fricke_mul_dilation
#print axioms inv_dilation_mul_fricke

end AsymptoticCongruenceLabels

namespace AsymptoticCongruenceStrip

open AsymptoticCongruenceLabels AsymptoticFreshMatrices

/-- The literal second degeneracy overgroup D_p⁻¹ Γ₀(M) D_p. -/
noncomputable def degeneracyGroup (M p : ℕ) (hp : 0<p) : Subgroup AsymptoticRationalGroup.Group :=
  (gamma M).map (MulAut.conj (dilationLabel p hp)⁻¹).toMonoidHom

theorem frickeOldGroup_eq_degeneracy (M p : ℕ) (hM : 0<M) (hp : 0<p) :
    frickeOldGroup (p*M) M (Nat.mul_pos hp hM)=degeneracyGroup M p hp := by
  have hf : (MulAut.conj (frickeLabel (p*M) (Nat.mul_pos hp hM))).toMonoidHom=
      (MulAut.conj (dilationLabel p hp)⁻¹).toMonoidHom.comp
        (MulAut.conj (frickeLabel M hM)).toMonoidHom := by
    apply MonoidHom.ext
    intro g
    change frickeLabel (p*M) _*g*(frickeLabel (p*M) _)⁻¹=
      (dilationLabel p hp)⁻¹*(frickeLabel M hM*g*(frickeLabel M hM)⁻¹)*((dilationLabel p hp)⁻¹)⁻¹
    rw [← inv_dilation_mul_fricke M p hM hp]
    group
  rw [frickeOldGroup,hf,← Subgroup.map_map,gamma_map_fricke,degeneracyGroup]

theorem gamma_le_degeneracyGroup (M p : ℕ) (hM : 0<M) (hp : 0<p) :
    gamma (p*M)≤degeneracyGroup M p hp := by
  rw [← frickeOldGroup_eq_degeneracy M p hM hp]
  exact gamma_le_frickeOldGroup (Nat.mul_pos hp hM) (Nat.dvd_mul_left M p)

theorem degeneracyGroup_index (M p : ℕ) (hM : 0<M) (hp : 0<p) :
    (gamma (p*M)).relIndex (degeneracyGroup M p hp)=(gamma (p*M)).relIndex (gamma M) := by
  rw [← frickeOldGroup_eq_degeneracy M p hM hp,frickeOldGroup_index]

#print axioms frickeOldGroup_eq_degeneracy
#print axioms gamma_le_degeneracyGroup
#print axioms degeneracyGroup_index

end AsymptoticCongruenceStrip
