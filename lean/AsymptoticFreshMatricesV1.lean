module

public import AsymptoticIntegralMatricesV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticFreshMatrices

open Matrix AsymptoticRationalGroup AsymptoticRationalFreeness AsymptoticRationalBranches
open AsymptoticIntegralSubgroup AsymptoticReconstructionBranch

/-- The integral representative of the fresh-prime matrix in the paper. -/
def entries (N q : ℕ) (a b c : ℤ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(N:ℚ)*a,-c;(N:ℚ)*q,-(N:ℚ)*b]

theorem entries_det (N q : ℕ) (a b c : ℤ) (h : (q:ℤ)*c=(N:ℤ)*a*b+1) :
    (entries N q a b c).det=(N:ℚ) := by
  rw [Matrix.det_fin_two]
  change ((N:ℚ)*a)*(-(N:ℚ)*b)-(-c)*((N:ℚ)*q)=(N:ℚ)
  have hh : (q:ℚ)*c=(N:ℚ)*a*b+1 := by exact_mod_cast h
  linear_combination (N:ℚ)*hh

def representative (N q : ℕ) (hN : N≠0) (a b c : ℤ) (h : (q:ℤ)*c=(N:ℤ)*a*b+1) :
    GL (Fin 2) ℚ := GeneralLinearGroup.mkOfDetNeZero (entries N q a b c)
      (by rw [entries_det N q a b c h]; exact_mod_cast hN)

theorem representative_det (N q : ℕ) (hN : N≠0) (a b c : ℤ) (h : (q:ℤ)*c=(N:ℤ)*a*b+1) :
    (representative N q hN a b c h).det.val=(N:ℚ) := entries_det N q a b c h

theorem representative_integral (N q : ℕ) [Fact q.Prime] (hN : N≠0) (hq : ¬q∣N)
    (a b c : ℤ) (h : (q:ℤ)*c=(N:ℤ)*a*b+1) : representative N q hN a b c h∈integralGL q := by
  apply integer_matrix_integral q _ !![(N:ℤ)*a,-c;(N:ℤ)*q,-(N:ℤ)*b]
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [representative,entries,GeneralLinearGroup.mkOfDetNeZero]
  · change padicNorm q (representative N q hN a b c h).det.val=1
    rw [representative_det]
    exact (padicNorm.nat_eq_one_iff N).mpr hq

/-- The literal T_(a/q) W_(Nq²) T_(-b/q) matrix, before scalar reduction. -/
def branchMatrix (N q : ℕ) (hN : N≠0) (hq : q≠0) (a b : ℤ) : GL (Fin 2) ℚ :=
  branch ((N:ℚ)*q^2) (-(b:ℚ)/q) ((a:ℚ)/q)
    (mul_ne_zero (by exact_mod_cast hN) (pow_ne_zero _ (by exact_mod_cast hq)))

theorem branchMatrix_scalar (N q : ℕ) (hN : N≠0) (hq : q≠0)
    (a b c : ℤ) (h : (q:ℤ)*c=(N:ℤ)*a*b+1) :
    representative N q hN a b c h *
      GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (q:ℚ) (by exact_mod_cast hq))=
    branchMatrix N q hN hq a b := by
  have hq' : (q:ℚ)≠0 := by exact_mod_cast hq
  have hh : (q:ℚ)*c=(N:ℚ)*a*b+1 := by exact_mod_cast h
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [representative,entries,branchMatrix,branch,GeneralLinearGroup.mkOfDetNeZero,
      GeneralLinearGroup.scalar,Matrix.scalar,Matrix.natCast_apply,Matrix.mul_apply]
  · field_simp
  · field_simp
    nlinarith [hh]
  · ring
  · field_simp

theorem rationalMap_scalar (u : ℚˣ) : rationalMap (GeneralLinearGroup.scalar (Fin 2) u)=1 := by
  unfold rationalMap
  rw [MonoidHom.comp_apply,GeneralLinearGroup.map_scalar,ProjGenLinGroup.mk_scalar]

theorem branchMatrix_projective (N q : ℕ) (hN : N≠0) (hq : q≠0)
    (a b c : ℤ) (h : (q:ℤ)*c=(N:ℤ)*a*b+1) :
    rationalMap (representative N q hN a b c h)=rationalMap (branchMatrix N q hN hq a b) := by
  rw [← branchMatrix_scalar N q hN hq a b c h,map_mul,rationalMap_scalar,mul_one]

theorem branchMatrix_positive (N q : ℕ) (hN : 0<N) (hq : 0<q) (a b : ℤ) :
    0<(realMatrix (branchMatrix N q hN.ne' hq.ne' a b)).det.val := by
  rw [branchMatrix,realMatrix_branch,branch_det]
  positivity

noncomputable def label (N q : ℕ) (hN : 0<N) (hq : 0<q) (a b : ℤ) :
    AsymptoticRationalGroup.Group :=
  ofMatrix (branchMatrix N q hN.ne' hq.ne' a b) (branchMatrix_positive N q hN hq a b)

/-- The actual positive projective fresh-prime label is q-integral,
although its unreduced matrix has denominators q. -/
theorem label_integral (N q : ℕ) [Fact q.Prime] (hN : 0<N) (hq : ¬q∣N)
    (a b c : ℤ) (h : (q:ℤ)*c=(N:ℤ)*a*b+1) :
    label N q hN (Fact.out : q.Prime).pos a b∈integralGroup q := by
  apply (integralGroup_mem_iff q _).mpr
  exact ⟨representative N q hN.ne' a b c h,representative_integral N q hN.ne' hq a b c h,
    branchMatrix_projective N q hN.ne' (Fact.out : q.Prime).ne_zero a b c h⟩

#print axioms entries_det
#print axioms representative_det
#print axioms representative_integral
#print axioms branchMatrix_scalar
#print axioms rationalMap_scalar
#print axioms branchMatrix_projective
#print axioms branchMatrix_positive
#print axioms label_integral

end AsymptoticFreshMatrices
