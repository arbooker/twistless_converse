module

public import QuantitativeMaassLowRankFilterLowerV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Module
open scoped InnerProductSpace

namespace QuantitativeMaass

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- The exact kernel projection is diagonal in the symmetric spectral basis. -/
theorem kernelProjection_eigenvector (S : E →ₗ[ℂ] E) (hS : S.IsSymmetric)
    (i : Fin (finrank ℂ E)) :
    S.ker.starProjection (hS.eigenvectorBasis rfl i)=
      if hS.eigenvalues rfl i=0 then hS.eigenvectorBasis rfl i else 0 := by
  classical
  by_cases hz : hS.eigenvalues rfl i=0
  · rw [ite_eq_left hz]
    apply Submodule.starProjection_eq_self_iff.mpr
    change S (hS.eigenvectorBasis rfl i)=0
    rw [hS.apply_eigenvectorBasis rfl,hz,RCLike.ofReal_zero,zero_smul]
  · rw [ite_eq_right hz]
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (S.ker.zero_mem)
    intro x hx
    simp only [sub_zero]
    have hh := hS (hS.eigenvectorBasis rfl i) x
    change S x=0 at hx
    rw [hx,inner_zero_right,hS.apply_eigenvectorBasis rfl,_root_.inner_smul_left] at hh
    have hn : starRingEnd ℂ (RCLike.ofReal (hS.eigenvalues rfl i))≠0 := by
      simpa using hz
    exact (mul_eq_zero.mp hh).resolve_left hn

/-- Affine polynomial filtering has its literal scalar eigenaction. -/
theorem affine_filter_eigenvector (S : E →ₗ[ℂ] E) (hS : S.IsSymmetric)
    (c : ℝ) (m : ℕ) (i : Fin (finrank ℂ E)) :
    ((1-(c:ℂ) • S)^m) (hS.eigenvectorBasis rfl i)=
      (((1-c*hS.eigenvalues rfl i)^m:ℝ):ℂ) • hS.eigenvectorBasis rfl i := by
  have hb : (1-(c:ℂ) • S) (hS.eigenvectorBasis rfl i)=
      ((1-c*hS.eigenvalues rfl i:ℝ):ℂ) • hS.eigenvectorBasis rfl i := by
    rw [LinearMap.sub_apply,Module.End.one_apply,LinearMap.smul_apply,hS.apply_eigenvectorBasis rfl,
      Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_mul]
    module
  induction m with
  | zero => simp only [pow_zero,Module.End.one_apply,Complex.ofReal_one,one_smul]
  | succ m ih =>
    rw [pow_succ,Module.End.mul_apply,hb,map_smul,ih,smul_smul]
    rw [pow_succ,Complex.ofReal_mul]
    congr 1
    ring

#print axioms kernelProjection_eigenvector
#print axioms affine_filter_eigenvector

end QuantitativeMaass
