module

public import AsymptoticFreshMatricesV1
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticFreshMatrices

open Matrix AsymptoticRationalGroup AsymptoticRationalFreeness AsymptoticRationalBranches
open AsymptoticReconstructionBranch UpperHalfPlane
open scoped MatrixGroups

/-- The individual congruence relation exposed by the fresh-prime
defect after using the untwisted Fricke equation. -/
def canonicalEntries (N q : ℕ) (a b c : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(q:ℤ),-b;-(N:ℤ)*a,c]

theorem canonical_det (N q : ℕ) (a b c : ℤ) (h : (q:ℤ)*c=(N:ℤ)*a*b+1) :
    (canonicalEntries N q a b c).det=1 := by
  rw [Matrix.det_fin_two]
  change (q:ℤ)*c-(-b)*(-(N:ℤ)*a)=1
  nlinarith [h]

def canonical (N q : ℕ) (a b c : ℤ) (h : (q:ℤ)*c=(N:ℤ)*a*b+1) : SL(2,ℤ) :=
  ⟨canonicalEntries N q a b c,canonical_det N q a b c h⟩

theorem canonical_mem_Gamma0 (N q : ℕ) (a b c : ℤ) (h : (q:ℤ)*c=(N:ℤ)*a*b+1) :
    canonical N q a b c h∈CongruenceSubgroup.Gamma0 N := by
  change (((-(N:ℤ)*a):ℤ):ZMod N)=0
  simp

def canonicalGL (N q : ℕ) (a b c : ℤ) (h : (q:ℤ)*c=(N:ℤ)*a*b+1) : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mkOfDetNeZero ((canonicalEntries N q a b c).map (fun z : ℤ => (z:ℚ))) (by
    rw [← Int.cast_det,canonical_det N q a b c h]
    norm_num)

theorem realMatrix_canonical_det (N q : ℕ) (a b c : ℤ) (h : (q:ℤ)*c=(N:ℤ)*a*b+1) :
    (realMatrix (canonicalGL N q a b c h)).det.val=1 := by
  change ((canonicalEntries N q a b c).map (fun z : ℤ => (z:ℝ))).det=1
  rw [← Int.cast_det,canonical_det N q a b c h]
  norm_num

noncomputable def canonicalLabel (N q : ℕ) (a b c : ℤ) (h : (q:ℤ)*c=(N:ℤ)*a*b+1) :
    AsymptoticRationalGroup.Group :=
  ofMatrix (canonicalGL N q a b c h) (by rw [realMatrix_canonical_det]; norm_num)

noncomputable def frickeLabel (N : ℕ) (hN : 0<N) : AsymptoticRationalGroup.Group :=
  ofMatrix (branch (N:ℚ) 0 0 (by exact_mod_cast hN.ne')) (by
    rw [realMatrix_branch,branch_det]
    exact_mod_cast hN)

theorem fricke_canonical (N q : ℕ) (hN : N≠0)
    (a b c : ℤ) (h : (q:ℤ)*c=(N:ℤ)*a*b+1) :
    branch (N:ℚ) 0 0 (by exact_mod_cast hN)*canonicalGL N q a b c h=
      representative N q hN a b c h := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [branch,canonicalGL,canonicalEntries,representative,entries,
      GeneralLinearGroup.mkOfDetNeZero,Matrix.mul_apply,Fin.sum_univ_two]

/-- The exact projective identity, including the scalar reduction of
the original branch. Thus these defects are genuine Γ₀(N) relations. -/
theorem label_eq_fricke_canonical (N q : ℕ) (hN : 0<N) (hq : 0<q)
    (a b c : ℤ) (h : (q:ℤ)*c=(N:ℤ)*a*b+1) :
    label N q hN hq a b=frickeLabel N hN*canonicalLabel N q a b c h := by
  apply Subtype.ext
  apply Subtype.ext
  change rationalMap (branchMatrix N q hN.ne' hq.ne' a b)=
    rationalMap (branch (N:ℚ) 0 0 _)*rationalMap (canonicalGL N q a b c h)
  rw [← map_mul,fricke_canonical]
  exact (branchMatrix_projective N q hN.ne' hq.ne' a b c h).symm

/-- On functions satisfying the Fricke law, the individual fresh
defect is precisely the corresponding congruence-invariance defect. -/
theorem fricke_defect_eq (N q : ℕ) (hN : 0<N) (hq : 0<q)
    (a b c : ℤ) (h : (q:ℤ)*c=(N:ℤ)*a*b+1)
    (F : ℍ → ℂ) (w : ℂ) (hF : ∀ z,w*F (frickeLabel N hN • z)=F z) (z : ℍ) :
    w*F (label N q hN hq a b • z)-F z=F (canonicalLabel N q a b c h • z)-F z := by
  rw [label_eq_fricke_canonical N q hN hq a b c h,mul_smul,hF]

#print axioms canonical_det
#print axioms canonical_mem_Gamma0
#print axioms realMatrix_canonical_det
#print axioms fricke_canonical
#print axioms label_eq_fricke_canonical
#print axioms fricke_defect_eq

end AsymptoticFreshMatrices
