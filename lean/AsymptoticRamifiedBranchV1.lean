module

public import AsymptoticCompactBranchFormulaV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRamifiedBranch

open UpperHalfPlane Matrix AsymptoticHyperbolicSlash

/-- The actual branch of the unnormalized ramified U operator. -/
def branch {K : Type*} [Field K] (p a : K) (hp : p≠0) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1,a;0,p] (by
    have hd : Matrix.det !![1,a;0,p]=p := by simp [Matrix.det_fin_two]
    rw [hd]
    exact hp)

theorem branch_det {K : Type*} [Field K] (p a : K) (hp : p≠0) :
    (branch p a hp).det.val=p := by
  change Matrix.det !![1,a;0,p]=p
  simp [Matrix.det_fin_two]

theorem branch_action {p : ℝ} (hp : 0<p) (a : ℝ) (z : ℍ) :
    ((branch p a hp.ne' • z:ℍ):ℂ)=((z:ℂ)+(a:ℂ))/(p:ℂ) := by
  rw [coe_smul_of_det_pos (by rw [branch_det]; exact hp)]
  change ((1:ℂ)*(z:ℂ)+(a:ℂ))/((0:ℂ)*(z:ℂ)+(p:ℂ))=_
  ring

theorem branch_im {p : ℝ} (hp : 0<p) (a : ℝ) (z : ℍ) :
    (branch p a hp.ne' • z).im=z.im/p := by
  have he := congrArg Complex.im (branch_action hp a z)
  simpa using he

theorem branch_phase {p : ℝ} (hp : 0<p) (a : ℝ) (k : ℕ) (z : ℍ) :
    phase (branch p a hp.ne') k z=1 := by
  have hd : denom (branch p a hp.ne') z=(p:ℂ) := by
    change (0:ℂ)*(z:ℂ)+(p:ℂ)=(p:ℂ)
    ring
  rw [phase,hd,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp,
    div_self (Complex.ofReal_ne_zero.mpr hp.ne'),one_pow]

theorem normalized_branch {p : ℝ} (hp : 0<p) (a : ℝ) (m : ℕ) (F : ℂ → ℂ) (z : ℍ) :
    phase (branch p a hp.ne') (2*m) z*((branch p a hp.ne' • z).im:ℂ)^m*
      F (branch p a hp.ne' • z:ℍ)=
        (z.im:ℂ)^m/(p:ℂ)^m*F (((z:ℂ)+(a:ℂ))/(p:ℂ)) := by
  rw [branch_phase hp,one_mul,branch_im hp,branch_action hp,Complex.ofReal_div,div_pow]

#print axioms branch_action
#print axioms branch_phase
#print axioms normalized_branch

end AsymptoticRamifiedBranch
