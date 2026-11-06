module

public import QuantitativeNewGapTreeArithmeticDilationV1
public import QuantitativeMaassHeckeTreeCosetsV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open Matrix QuantitativeMaass AsymptoticRationalGroup AsymptoticRationalFreeness
open AsymptoticFreshMatrices AsymptoticRationalBranches AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open scoped MatrixGroups

/-- The actual rational matrix and projective label of a positive upper
triangular integral Hecke word. -/
def wordGL (R : HeckeUpper) (hR : 0 < R.det) : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mkOfDetNeZero (R.matrix.map (Int.castRingHom ℚ)) (by
    change (R.matrix.map (fun z : ℤ => (z : ℚ))).det ≠ 0
    rw [← Int.cast_det,HeckeUpper.det_matrix]
    exact_mod_cast hR.ne')

theorem wordGL_positive (R : HeckeUpper) (hR : 0 < R.det) :
    0 < (realMatrix (wordGL R hR)).det.val := by
  change 0 < (R.matrix.map (fun z : ℤ => (z : ℝ))).det
  rw [← Int.cast_det,HeckeUpper.det_matrix]
  exact_mod_cast hR

def wordLabel (R : HeckeUpper) (hR : 0 < R.det) : AsymptoticRationalGroup.Group :=
  ofMatrix (wordGL R hR) (wordGL_positive R hR)

/-- Membership of the concrete projective word in Gamma0 is precisely
the already counted projective integral-matrix identity condition. -/
theorem wordLabel_mem_gamma_iff (M : ℕ) (R : HeckeUpper) (hR : 0 < R.det) :
    wordLabel R hR ∈ gamma M ↔ HeckeUpper.projectiveGamma M R := by
  constructor
  · rintro ⟨A,hA,he⟩
    have hp : ProjGenLinGroup.mk (realMatrix (wordGL R hR)) =
        ProjGenLinGroup.mk (realMatrix (rationalGL A)) :=
      (congrArg (fun g : AsymptoticRationalGroup.Group => g.val.val) he).symm
    obtain ⟨u,hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hp
    have ent (i j : Fin 2) : (R.matrix i j : ℝ)*(u : ℝ)=(A.val i j : ℝ) := by
      have hh := congrArg (fun C : GL (Fin 2) ℝ => C.val i j) hu
      simpa [realMatrix,wordGL,rationalGL,GeneralLinearGroup.map,GeneralLinearGroup.mkOfDetNeZero,
        GeneralLinearGroup.scalar,Matrix.scalar,Matrix.mul_diagonal] using hh
    have h10 : A.val 1 0=0 := by
      have hh := ent 1 0
      have hz : R.matrix 1 0=0 := rfl
      rw [hz,Int.cast_zero,zero_mul] at hh
      exact_mod_cast hh.symm
    have hd : A.val 0 0*A.val 1 1=1 := by
      have hh := A.property
      simpa only [Matrix.det_fin_two,h10,mul_zero,sub_zero] using hh
    have hdiag : A.val 0 0=A.val 1 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' hd with ⟨h0,h1⟩ | ⟨h0,h1⟩ <;> rw [h0,h1]
    have hsq : (A.val 1 1 : ℝ)^2=1 := by
      have hh : (A.val 1 1)^2=1 := by simpa only [hdiag,pow_two] using hd
      exact_mod_cast hh
    have h00 := ent 0 0
    have h01 := ent 0 1
    have h11 := ent 1 1
    change (R.a : ℝ)*(u : ℝ)=(A.val 0 0 : ℝ) at h00
    change (R.b : ℝ)*(u : ℝ)=(A.val 0 1 : ℝ) at h01
    change (R.d : ℝ)*(u : ℝ)=(A.val 1 1 : ℝ) at h11
    have ha : R.a=R.d := by
      have hh : (R.a : ℝ)=(R.d : ℝ) := mul_right_cancel₀ u.ne_zero
        (h00.trans ((congrArg (fun z : ℤ => (z : ℝ)) hdiag).trans h11.symm))
      exact_mod_cast hh
    have hb : R.b=R.d*(A.val 0 1*A.val 1 1) := by
      have hh : (R.b : ℝ)=(R.d : ℝ)*((A.val 0 1 : ℝ)*(A.val 1 1 : ℝ)) := by
        apply mul_right_cancel₀ u.ne_zero
        rw [h01]
        calc
          (A.val 0 1 : ℝ) = (A.val 1 1 : ℝ)*((A.val 0 1 : ℝ)*(A.val 1 1 : ℝ)) := by
            calc
              (A.val 0 1 : ℝ) = (A.val 0 1 : ℝ)*(A.val 1 1 : ℝ)^2 := by rw [hsq,mul_one]
              _ = _ := by ring
          _ = _ := by rw [← h11]; ring
      exact_mod_cast hh
    exact (HeckeUpper.projectiveGamma_iff_translation M R hR.ne').mpr ⟨ha,_,hb⟩
  · rintro ⟨c,hc,A,hA,he⟩
    have hm : wordGL R hR = GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc)*rationalGL A := by
      apply Units.ext
      change R.matrix.map (Int.castRingHom ℚ) =
        (GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc)).val*(rationalGL A).val
      rw [he]
      change c • A.val.map (Int.castRingHom ℚ) =
        Matrix.diagonal (fun _ : Fin 2 => c)*A.val.map (fun z : ℤ => (z : ℚ))
      ext i j
      simp only [Matrix.diagonal_mul,Matrix.smul_apply,smul_eq_mul]
      rfl
    have hl : wordLabel R hR=integralLabel A := by
      apply Subtype.ext
      apply Subtype.ext
      change rationalMap (wordGL R hR)=rationalMap (rationalGL A)
      rw [hm,map_mul,rationalMap_scalar,one_mul]
    rw [hl]
    exact ⟨A,hA,rfl⟩

def heckeBranchLabel (p : ℕ) (hp : 0 < p) : Option (ZMod p) → AsymptoticRationalGroup.Group
  | none => dilationLabel p hp
  | some a => upperHeckeLabel p hp a.val

theorem word_left_pos (p : ℕ) (hp : 0 < p) (j : Option (ZMod p))
    (R : HeckeUpper) (hR : 0 < R.det) : 0 < (HeckeUpper.left p j R).det := by
  rw [HeckeUpper.left_det]
  exact mul_pos (by exact_mod_cast hp) hR

/-- Literal branch multiplication agrees with the integral word recursion. -/
theorem wordLabel_left (p : ℕ) (hp : 0 < p) (j : Option (ZMod p))
    (R : HeckeUpper) (hR : 0 < R.det) :
    wordLabel (HeckeUpper.left p j R) (word_left_pos p hp j R hR) =
      heckeBranchLabel p hp j*wordLabel R hR := by
  apply Subtype.ext
  apply Subtype.ext
  cases j with
  | none =>
    change rationalMap (wordGL _ _)=rationalMap (dilationGL p hp)*rationalMap (wordGL R hR)
    rw [← map_mul]
    congr 1
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [wordGL,dilationGL,GeneralLinearGroup.mkOfDetNeZero,HeckeUpper.left,
        HeckeUpper.matrix,Matrix.mul_apply,Fin.sum_univ_two]
  | some a =>
    change rationalMap (wordGL _ _)=rationalMap (upperHeckeGL p hp a.val)*rationalMap (wordGL R hR)
    rw [← map_mul]
    congr 1
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [wordGL,upperHeckeGL,GeneralLinearGroup.mkOfDetNeZero,HeckeUpper.left,
        HeckeUpper.matrix,Matrix.mul_apply,Fin.sum_univ_two]

#print axioms wordLabel_mem_gamma_iff
#print axioms wordLabel_left

end QuantitativeNewGap
