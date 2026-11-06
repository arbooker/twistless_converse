module

public import SmallLevelThirtySixHeckeOriginalV1
public import SmallLevelAnalyticRigidityTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace SmallLevelThirtySix

open UpperHalfPlane ModularGroup FinitenessOriginalInput
open scoped ModularForm MatrixGroups Manifold

/-- Conversion of the analytic five-branch criterion to the actual Mathlib
slash action. This includes the determinant normalization in that action. -/
theorem slash_filter_zero (k : ℕ) (hk : 0<k) (H : ℍ → ℂ) (lam : ℂ)
    (hhol : MDiff H) (hT : H ∣[(k:ℤ)] T=H) (hS : H ∣[(k:ℤ)] ModularGroup.S=H)
    (he : (H ∣[(k:ℤ)] heckeInfinity)-(2:ℂ) • (H ∣[(k:ℤ)] heckeFinite 1)+
      (H ∣[(k:ℤ)] heckeFinite 2)-(H ∣[(k:ℤ)] heckeFinite 3)+
      (H ∣[(k:ℤ)] heckeFinite 4)+lam • H=0) : H=0 := by
  let F : ℂ → ℂ := H ∘ ofComplex
  have hr (w : ℍ) : H w=F (w:ℂ) := by simp [F]
  have ha : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im} :=
    (UpperHalfPlane.mdifferentiable_iff.mp hhol).analyticOnNhd isOpen_upperHalfPlaneSet
  have hp (z : ℂ) (hz : 0<z.im) : F (z+1)=F z := by
    have hh := congrFun hT (⟨z,hz⟩ : ℍ)
    rw [ModularForm.SL_slash_apply] at hh
    have hd : denom T (⟨z,hz⟩ : ℍ)=1 := by
      norm_num [denom, ModularGroup.T, Matrix.SpecialLinearGroup.toGL,
        Matrix.SpecialLinearGroup.map_apply_coe]
    rw [hd, one_zpow, mul_one, hr, hr, modular_T_smul] at hh
    simpa only [coe_vadd, Complex.ofReal_one, coe_mk, add_comm] using hh
  have hs (z : ℂ) (hz : 0<z.im) : F (-1/z)=z^k*F z := by
    have hh := congrFun hS (⟨z,hz⟩ : ℍ)
    rw [ModularForm.SL_slash_apply, denom_S, hr, hr, modular_S_smul] at hh
    simp only [inv_neg, zpow_neg, zpow_natCast] at hh
    have hz0 : z≠0 := by intro heq; simp [heq] at hz
    have hzpow : z^k≠0 := pow_ne_zero _ hz0
    have hx := congrArg (fun v : ℂ => v*z^k) hh
    simp only [mul_assoc, inv_mul_cancel₀ hzpow, mul_one] at hx
    simpa only [mul_comm, neg_div, one_div] using hx
  have heq (z : ℂ) (hz : 0<z.im) :
      (5:ℂ)^k*F (5*z)-2*F ((z+6)/5)+F ((z+12)/5)-F ((z+18)/5)+
        F ((z+24)/5)+(5*lam)*F z=0 := by
    have hh := congrFun he (⟨z,hz⟩ : ℍ)
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
      finite_branch_slash, infinity_branch_slash] at hh
    simp only [hr, finite_branch_point, infinity_branch_point,
      Int.cast_ofNat] at hh
    norm_num only [mul_one, show (6:ℂ)*2=12 by norm_num,
      show (6:ℂ)*3=18 by norm_num, show (6:ℂ)*4=24 by norm_num] at hh
    linear_combination 5*hh
  funext z
  rw [hr]
  exact SmallLevelAnalyticRigidity.hecke_filter_eq_zero ha hk hp hs heq z z.im_pos

/-- The negative-sign level-36 extension vanishes for every original
Euler-product solution, including zero Hecke-5 eigenvalue. -/
theorem original_obstruction_zero {f : ℕ → ℂ} (m : ℕ) (hm : 0<m)
    (hf : IsSolution 36 (2*m) f)
    (hS : scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] ModularGroup.S= -scaledFunction (2*m) f) :
    obstruction m (scaledFunction (2*m) f)=0 := by
  have hT := scaledFunction_quadratic hf.toEulerData (2*m)
  have hi := obstruction_invariant m (scaledFunction (2*m) f) hT hS
  exact slash_filter_zero (2*m) (by omega) _ _
    (obstruction_holomorphic (scaledFunction_holomorphic hf.toEulerData)) hi.2 hi.1
    (obstruction_hecke m (scaledFunction (2*m) f) _ hT hS
      (original_hecke_five hf.toEulerData m))

#print axioms slash_filter_zero
#print axioms original_obstruction_zero

end SmallLevelThirtySix
