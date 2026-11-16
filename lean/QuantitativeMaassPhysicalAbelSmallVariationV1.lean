module

public import QuantitativeMaassAbelRadialDerivativeV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- A physical second-derivative bound controls the Abel derivative. The
ordinary derivative at q=1 is neither assumed nor sampled. -/
theorem abelProfile_derivative_norm_physical (F : ℝ → ℂ) (B M : ℝ)
    (hB : 1≤B) (hs : Function.support F⊆Iic B)
    (hb : ∀ q,1<q → ‖deriv (deriv F) q‖≤M) (q : ℝ) (hq : 1≤q) :
    ‖abelProfile (deriv F) q‖≤(Real.sqrt 2/Real.pi)*(M*(B+1)) := by
  have hd : Function.support (deriv F)⊆Iic B :=
    support_deriv_subset.trans (closure_minimal hs isClosed_Iic)
  have hdd : Function.support (deriv (deriv F))⊆Iic B :=
    support_deriv_subset.trans (closure_minimal hd isClosed_Iic)
  have hi := norm_setIntegral_le_of_norm_le_const (μ:=volume) (s:=Ioc (0:ℝ) (B+1))
    (f:=fun s => deriv (deriv F) (q+s^2)) (by simp) (fun s hs0 =>
      hb _ (by nlinarith [sq_pos_of_pos hs0.1]))
  rw [Real.volume_real_Ioc_of_le (by linarith : 0≤B+1),sub_zero] at hi
  rw [abelProfile,abelIntegral_physical_interval _ B hB hdd q hq,norm_mul,norm_neg]
  have hn : ‖(Real.sqrt 2/Real.pi:ℂ)‖=Real.sqrt 2/Real.pi := by
    rw [← Complex.ofReal_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  rw [hn]
  exact mul_le_mul_of_nonneg_left hi (by positivity)

/-- An explicit initial radial variation bound. This is an intermediate
estimate: its second-derivative premise must be established for each time profile. -/
theorem abelProfile_initial_radial_variation (F : ℝ → ℂ)
    (hF : ContDiffOn ℝ ∞ F (Ici 1)) (B M δ : ℝ) (hB : 1≤B) (hM : 0≤M) (hδ : 0≤δ)
    (hs : Function.support F⊆Iic B)
    (hb : ∀ q,1<q → ‖deriv (deriv F) q‖≤M) :
    (∫ r in 0..δ,‖deriv (fun r => abelProfile F (Real.cosh r)) r‖)≤
      (Real.sqrt 2/Real.pi)*(M*(B+1))*(Real.cosh δ-1) := by
  let k := fun r => abelProfile F (Real.cosh r)
  let C := (Real.sqrt 2/Real.pi)*(M*(B+1))
  have hC : 0≤C := by dsimp only [C];positivity
  have hk : ContDiff ℝ ∞ k := ContDiffOn.comp_contDiff (g:=abelProfile F) (f:=Real.cosh)
    (abelProfile_smoothOn_physical F hF B hB hs) (by fun_prop) (fun r => Real.one_le_cosh r)
  have hi := ((contDiff_infty_iff_deriv.mp hk).2.continuous.norm).intervalIntegrable (μ:=volume) 0 δ
  have hj := (Real.continuous_sinh.const_mul C).intervalIntegrable (μ:=volume) 0 δ
  have hh := intervalIntegral.integral_mono_on hδ hi hj (fun r hr => by
    by_cases hz : r=0
    · subst r
      have he : Function.Even k := by intro u;simp only [k,Real.cosh_neg]
      rw [even_time_deriv_zero k he,Real.sinh_zero,mul_zero,norm_zero]
    · have hp : 0<r := lt_of_le_of_ne hr.1 (Ne.symm hz)
      have hd := (abelProfile_hasDerivAt_physical F hF B hB hs (Real.cosh r)
        (Real.one_lt_cosh.mpr hp.ne')).scomp r (Real.hasDerivAt_cosh r)
      simp only [Function.comp_def] at hd
      change ‖deriv (fun r => abelProfile F (Real.cosh r)) r‖≤_
      rw [hd.deriv,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.sinh_pos_iff.mpr hp)]
      exact (mul_le_mul_of_nonneg_left (abelProfile_derivative_norm_physical F B M hB hs hb _
        (Real.one_le_cosh r)) (Real.sinh_pos_iff.mpr hp).le).trans_eq (mul_comm _ _))
  rw [intervalIntegral.integral_const_mul] at hh
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r (_ : r∈uIcc (0:ℝ) δ) => Real.hasDerivAt_cosh r)
    (Real.continuous_sinh.intervalIntegrable (μ:=volume) 0 δ)
  rw [he,Real.cosh_zero] at hh
  exact hh

#print axioms abelProfile_derivative_norm_physical
#print axioms abelProfile_initial_radial_variation

end QuantitativeMaass
