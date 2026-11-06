module

public import SmallLevelOddFrickeV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelThree

open Matrix UpperHalfPlane
open scoped MatrixGroups ModularForm

def lowerBranch (N : ℕ) (j : ℤ) : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mkOfDetNeZero !![3,0;(j:ℝ)*N,1] (by norm_num [det_fin_two])

theorem lowerBranch_det (N : ℕ) (j : ℤ) : (GeneralLinearGroup.det (lowerBranch N j):ℝ)=3 := by
  simp [lowerBranch, det_fin_two]

theorem lowerBranch_point (N : ℕ) (j : ℤ) (z : ℍ) :
    ((lowerBranch N j • z : ℍ):ℂ)=3*(z:ℂ)/((j:ℂ)*N*(z:ℂ)+1) := by
  rw [coe_smul_of_det_pos (by rw [lowerBranch_det]; norm_num)]
  change ((3:ℂ)*(z:ℂ)+0)/((((j:ℝ)*(N:ℝ):ℝ):ℂ)*(z:ℂ)+1)=_
  push_cast
  ring

theorem lowerBranch_denom (N : ℕ) (j : ℤ) (z : ℍ) :
    denom (lowerBranch N j) z=(j:ℂ)*N*(z:ℂ)+1 := by
  simp [denom, lowerBranch, GeneralLinearGroup.mkOfDetNeZero]

/-- The Fricke equation evaluated at a lower determinant-three branch.
This identity has no division by its root number. -/
theorem lowerBranch_fricke {N k : ℕ} (hN : 0<N) (F : ℂ → ℂ) (χ : ℂ)
    (hfr : ∀ z : ℂ, 0<z.im → F z=
      χ/(((Real.sqrt N:ℂ)*z)^k)*F (-1/((N:ℂ)*z)))
    (j : ℤ) (z : ℍ) :
    (3:ℂ)^k * (F ((lowerBranch N j • z : ℍ):ℂ)/((j:ℂ)*N*(z:ℂ)+1)^k)=
      χ/(((Real.sqrt N:ℂ)*(z:ℂ))^k)*F (-1/(3*(N:ℂ)*(z:ℂ))-(j:ℂ)/3) := by
  have hn : (N:ℂ)≠0 := Nat.cast_ne_zero.mpr hN.ne'
  have hs : (Real.sqrt N:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
  have hz : (z:ℂ)≠0 := z.ne_zero
  have hd : (j:ℂ)*N*(z:ℂ)+1≠0 := by
    rw [← lowerBranch_denom]
    exact denom_ne_zero _ _
  let w : ℍ := lowerBranch N j • z
  have hw : (w:ℂ)=3*(z:ℂ)/((j:ℂ)*N*(z:ℂ)+1) := lowerBranch_point N j z
  have hi : -1/((N:ℂ)*(w:ℂ))= -1/(3*(N:ℂ)*(z:ℂ))-(j:ℂ)/3 := by
    rw [hw]
    field_simp
    ring
  have he := hfr w w.im_pos
  rw [hi] at he
  have hfactor : ((Real.sqrt N:ℂ)*(w:ℂ))=
      (3*((Real.sqrt N:ℂ)*(z:ℂ)))/((j:ℂ)*N*(z:ℂ)+1) := by rw [hw]; ring
  rw [hfactor, div_pow, mul_pow] at he
  change (3:ℂ)^k*(F w/((j:ℂ)*N*(z:ℂ)+1)^k)=_
  rw [he]
  field_simp
  have hd' : (z:ℂ)*(j:ℂ)*N+1≠0 := by
    convert hd using 1
    ring
  field_simp [hd']

#print axioms lowerBranch_point
#print axioms lowerBranch_fricke

end SmallLevelThree
