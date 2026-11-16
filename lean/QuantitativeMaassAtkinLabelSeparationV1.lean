module

public import QuantitativeMaassCompletedSectorSignsV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Matrix AsymptoticRationalGroup AsymptoticRationalFreeness AsymptoticRationalBranches
open AsymptoticReconstructionBranch
open AsymptoticFreshMatrices AsymptoticSectorSigns QuantitativeNewGap
open scoped MatrixGroups

namespace QuantitativeMaass

theorem exactAtkinLabel_divisor_injective (D Q D' Q' : ℕ) (hQ : 0<Q) (hQ' : 0<Q')
    (A B A' B' : ℤ) (hAB : (Q:ℤ)*A+(D:ℤ)*B=1) (hAB' : (Q':ℤ)*A'+(D':ℤ)*B'=1)
    (he : exactAtkinLabel D Q hQ A B hAB=exactAtkinLabel D' Q' hQ' A' B' hAB') : Q=Q' := by
  have hp := congrArg (fun g : AsymptoticRationalGroup.Group => g.val.val) he
  change ProjGenLinGroup.mk (realMatrix (exactAtkinGL D Q hQ A B hAB))=
    ProjGenLinGroup.mk (realMatrix (exactAtkinGL D' Q' hQ' A' B' hAB')) at hp
  obtain ⟨u,hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hp
  have h00 := congrArg (fun M : GL (Fin 2) ℝ => M.val 0 0) hu
  have hentry : (Q:ℝ)*(u:ℝ)=(Q':ℝ) := by
    simpa [realMatrix,exactAtkinGL,exactAtkinMatrix,GeneralLinearGroup.map,
      GeneralLinearGroup.mkOfDetNeZero,GeneralLinearGroup.scalar,Matrix.scalar,Matrix.mul_diagonal] using h00
  have hd1 : (realMatrix (exactAtkinGL D Q hQ A B hAB)).val.det=(Q:ℝ) := by
    rw [exactAtkinGL_real_val,←Int.cast_det,exactAtkinMatrix_det D Q A B hAB]
    norm_cast
  have hd2 : (realMatrix (exactAtkinGL D' Q' hQ' A' B' hAB')).val.det=(Q':ℝ) := by
    rw [exactAtkinGL_real_val,←Int.cast_det,exactAtkinMatrix_det D' Q' A' B' hAB']
    norm_cast
  have hd := congrArg (fun M : GL (Fin 2) ℝ => M.val.det) hu
  change ((realMatrix (exactAtkinGL D Q hQ A B hAB)).val*
    (GeneralLinearGroup.scalar (Fin 2) u).val).det=_ at hd
  rw [Matrix.det_mul,hd1,hd2] at hd
  have hdet : (Q:ℝ)*(u:ℝ)^2=(Q':ℝ) := by
    simpa [GeneralLinearGroup.scalar,Matrix.scalar,Matrix.det_fin_two,pow_two] using hd
  have hmul := congrArg (fun t : ℝ => t*(u:ℝ)) hentry
  have hu1 : (u:ℝ)=1 := by
    have hz : (Q':ℝ)≠0 := by exact_mod_cast hQ'.ne'
    apply mul_left_cancel₀ hz
    nlinarith [hmul,hdet]
  rw [hu1,mul_one] at hentry
  exact_mod_cast hentry

theorem exactAtkinLabel_ne_fricke (N D Q : ℕ) (hN : 0<N) (hQ : 0<Q)
    (A B : ℤ) (hAB : (Q:ℤ)*A+(D:ℤ)*B=1) :
    exactAtkinLabel D Q hQ A B hAB≠frickeLabel N hN := by
  intro he
  have hp := congrArg (fun g : AsymptoticRationalGroup.Group => g.val.val) he
  change ProjGenLinGroup.mk (realMatrix (exactAtkinGL D Q hQ A B hAB))=
    ProjGenLinGroup.mk (realMatrix (branch (N:ℚ) 0 0 _)) at hp
  obtain ⟨u,hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hp
  have h00 := congrArg (fun M : GL (Fin 2) ℝ => M.val 0 0) hu
  have hz : (Q:ℝ)*(u:ℝ)=0 := by
    simpa [realMatrix,exactAtkinGL,exactAtkinMatrix,branch,GeneralLinearGroup.map,
      GeneralLinearGroup.mkOfDetNeZero,GeneralLinearGroup.scalar,Matrix.scalar,Matrix.mul_diagonal] using h00
  exact (mul_ne_zero (by exact_mod_cast hQ.ne') u.ne_zero) hz

theorem simpleAtkinGeneratorIndex_injective (N : ℕ) (hN : 0<N) :
    Function.Injective (simpleAtkinGeneratorIndex N hN) := by
  intro p q he
  apply Subtype.ext
  exact exactAtkinLabel_divisor_injective _ _ _ _ _ _ _ _ _ _ _ _ (congrArg Subtype.val he)

theorem simpleAtkinGeneratorIndex_ne_fricke (N : ℕ) (hN : 0<N) (p : SimplePrime N) :
    simpleAtkinGeneratorIndex N hN p≠frickeGeneratorIndex N hN := by
  intro he
  exact exactAtkinLabel_ne_fricke N _ _ hN _ _ _ _ (congrArg Subtype.val he)

#print axioms exactAtkinLabel_divisor_injective
#print axioms exactAtkinLabel_ne_fricke
#print axioms simpleAtkinGeneratorIndex_injective
#print axioms simpleAtkinGeneratorIndex_ne_fricke

end QuantitativeMaass
