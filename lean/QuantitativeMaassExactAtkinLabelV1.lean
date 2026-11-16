module

public import QuantitativeMaassExactAtkinCuspV1
public import AsymptoticAtkinLehnerSquareV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Matrix UpperHalfPlane AsymptoticRationalGroup AsymptoticRationalFreeness
open AsymptoticRationalBranches AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open AsymptoticAtkinLehner AsymptoticReconstructionBranch
open scoped MatrixGroups

namespace QuantitativeMaass

def exactAtkinGL (D Q : ℕ) (hQ : 0<Q) (A B : ℤ)
    (hAB : (Q:ℤ)*A+(D:ℤ)*B=1) : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mkOfDetNeZero ((exactAtkinMatrix D Q A B).map (fun z : ℤ => (z:ℚ))) (by
    rw [←Int.cast_det,exactAtkinMatrix_det D Q A B hAB]
    exact_mod_cast hQ.ne')

theorem exactAtkinGL_real_val (D Q : ℕ) (hQ : 0<Q) (A B : ℤ)
    (hAB : (Q:ℤ)*A+(D:ℤ)*B=1) :
    (realMatrix (exactAtkinGL D Q hQ A B hAB)).val=
      (exactAtkinMatrix D Q A B).map (fun z : ℤ => (z:ℝ)) := by
  ext i j
  simp [realMatrix,exactAtkinGL,GeneralLinearGroup.map,GeneralLinearGroup.mkOfDetNeZero]

theorem exactAtkinGL_positive (D Q : ℕ) (hQ : 0<Q) (A B : ℤ)
    (hAB : (Q:ℤ)*A+(D:ℤ)*B=1) : 0<(realMatrix (exactAtkinGL D Q hQ A B hAB)).det.val := by
  change 0<(realMatrix (exactAtkinGL D Q hQ A B hAB)).val.det
  rw [exactAtkinGL_real_val,←Int.cast_det,exactAtkinMatrix_det D Q A B hAB]
  exact_mod_cast hQ

def exactAtkinLabel (D Q : ℕ) (hQ : 0<Q) (A B : ℤ)
    (hAB : (Q:ℤ)*A+(D:ℤ)*B=1) : AsymptoticRationalGroup.Group :=
  ofMatrix (exactAtkinGL D Q hQ A B hAB) (exactAtkinGL_positive D Q hQ A B hAB)

/-- The new literal matrix representative is the already checked local
Atkin--Lehner projective transformation, including composite exact divisors. -/
theorem exactAtkinLabel_eq_localAtkin (D Q : ℕ) (hD : 0<D) (hQ : 0<Q) (A B : ℤ)
    (hAB : (Q:ℤ)*A+(D:ℤ)*B=1) :
    exactAtkinLabel D Q hQ A B hAB=localAtkin D Q hD hQ A B hAB := by
  have hN : ((Q*D:ℕ):ℚ)≠0 := by exact_mod_cast (Nat.mul_pos hQ hD).ne'
  have hDz : -(D:ℚ)≠0 := neg_ne_zero.mpr (by exact_mod_cast hD.ne')
  have he : branch ((Q*D:ℕ):ℚ) 0 0 hN*complementGL D Q hD A B hAB=
      exactAtkinGL D Q hQ A B hAB*GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (-(D:ℚ)) hDz) := by
    apply Units.ext
    change (branch ((Q*D:ℕ):ℚ) 0 0 hN).val*(complementGL D Q hD A B hAB).val=
      (exactAtkinGL D Q hQ A B hAB).val*
        (GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (-(D:ℚ)) hDz)).val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [branch,complementGL,AsymptoticFreshMatrices.representative,
        AsymptoticFreshMatrices.entries,exactAtkinGL,exactAtkinMatrix,
        GeneralLinearGroup.mkOfDetNeZero,GeneralLinearGroup.scalar,Matrix.scalar,
        Matrix.mul_apply,Fin.sum_univ_two]
    all_goals ring
  apply Subtype.ext
  apply Subtype.ext
  change rationalMap (exactAtkinGL D Q hQ A B hAB)=
    rationalMap (branch ((Q*D:ℕ):ℚ) 0 0 hN)*rationalMap (complementGL D Q hD A B hAB)
  rw [←map_mul,he,map_mul,AsymptoticFreshMatrices.rationalMap_scalar,mul_one]

theorem exactAtkinLabel_normalizes (D Q : ℕ) (hD : 0<D) (hQ : 0<Q) (A B : ℤ)
    (hAB : (Q:ℤ)*A+(D:ℤ)*B=1) :
    (∀ b∈gamma (Q*D),exactAtkinLabel D Q hQ A B hAB*b*
      (exactAtkinLabel D Q hQ A B hAB)⁻¹∈gamma (Q*D)) ∧
    (∀ b∈gamma (Q*D),(exactAtkinLabel D Q hQ A B hAB)⁻¹*b*
      exactAtkinLabel D Q hQ A B hAB∈gamma (Q*D)) := by
  rw [exactAtkinLabel_eq_localAtkin D Q hD hQ A B hAB]
  exact ⟨fun _ hb => local_conj_mem D Q hD hQ A B hAB hb,
    fun _ hb => local_inv_conj_mem D Q hD hQ A B hAB hb⟩

theorem upper_triangular_height_scale (g : GL (Fin 2) ℝ) (hc : g.val 1 0=0) :
    ∃ C : ℝ,0<C ∧ ∀ z : ℍ,(g • z).im=C*z.im := by
  have hd : g.val 1 1≠0 := by
    intro h
    have hn := g.det_ne_zero
    simp [Matrix.det_fin_two,hc,h] at hn
  refine ⟨|g.det.val|/(g.val 1 1)^2,div_pos (abs_pos.mpr g.det_ne_zero) (sq_pos_of_ne_zero hd),?_⟩
  intro z
  rw [UpperHalfPlane.im_smul_eq_div_normSq]
  simp only [UpperHalfPlane.denom,hc,Complex.ofReal_zero,zero_mul,zero_add,
    Complex.normSq_ofReal]
  ring

theorem exactAtkin_cusp_height (D Q : ℕ) (hQ : 0<Q) (A B : ℤ)
    (hAB : (Q:ℤ)*A+(D:ℤ)*B=1) (a b : SL(2,ℤ))
    (hzero : (b.val*exactAtkinMatrix D Q A B*a.val) 1 0=0) :
    ∃ C : ℝ,0<C ∧ ∀ z : ℍ,
      ((integralLabel b*exactAtkinLabel D Q hQ A B hAB*integralLabel a) • z).im=C*z.im := by
  let R := realMatrix (rationalGL b*exactAtkinGL D Q hQ A B hAB*rationalGL a)
  have hi (c : SL(2,ℤ)) : (realMatrix (rationalGL c)).val=c.val.map (fun x : ℤ => (x:ℝ)) := by
    ext i j
    simp [realMatrix,GeneralLinearGroup.map,rationalGL_apply]
  have hval : R.val=(b.val*exactAtkinMatrix D Q A B*a.val).map (fun x : ℤ => (x:ℝ)) := by
    dsimp only [R,realMatrix]
    rw [map_mul,map_mul]
    change (realMatrix (rationalGL b)).val*(realMatrix (exactAtkinGL D Q hQ A B hAB)).val*
      (realMatrix (rationalGL a)).val=_
    rw [hi,hi,exactAtkinGL_real_val]
    ext i j
    simp [Matrix.mul_apply,Fin.sum_univ_two]
  have hz : R.val 1 0=0 := by rw [hval]; simp only [Matrix.map_apply,hzero,Int.cast_zero]
  obtain ⟨C,hC,hscale⟩ := upper_triangular_height_scale R hz
  refine ⟨C,hC,?_⟩
  intro z
  have he : (integralLabel b*exactAtkinLabel D Q hQ A B hAB*integralLabel a) • z=R • z := by
    change (rationalMap (rationalGL b)*rationalMap (exactAtkinGL D Q hQ A B hAB)*
      rationalMap (rationalGL a)) • z=R • z
    simp only [←map_mul]
    exact pglMk_smul _ _
  rw [he,hscale]

#print axioms exactAtkinGL_real_val
#print axioms exactAtkinGL_positive
#print axioms exactAtkinLabel_eq_localAtkin
#print axioms exactAtkinLabel_normalizes
#print axioms upper_triangular_height_scale
#print axioms exactAtkin_cusp_height

end QuantitativeMaass
