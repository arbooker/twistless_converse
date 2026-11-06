module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public section

namespace AsymptoticBergmanDecay

open UpperHalfPlane Filter
open scoped Topology

/-- The normalized upper-half-plane Bergman kernel before its k-th power.
The scalar prefactor (k-1)/(4π) is kept separate. -/
noncomputable def base (z u : ℍ) : ℂ :=
  (2*Complex.I*(Real.sqrt (z.im*u.im):ℂ))/((z:ℂ)-star (u:ℂ))

theorem denominator_ne_zero (z u : ℍ) : (z:ℂ)-star (u:ℂ)≠0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im,Complex.star_def,Complex.conj_im,UpperHalfPlane.coe_im,
    Complex.zero_im,sub_neg_eq_add] at hi
  linarith [z.im_pos,u.im_pos]

theorem denominator_square (z u : ℍ) :
    ‖(z:ℂ)-star (u:ℂ)‖^2=‖(z:ℂ)-(u:ℂ)‖^2+4*z.im*u.im := by
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
    Complex.star_def,Complex.conj_re,Complex.conj_im,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
  ring

theorem norm_base (z u : ℍ) :
    ‖base z u‖=2*Real.sqrt (z.im*u.im)/‖(z:ℂ)-star (u:ℂ)‖ := by
  simp [base,Complex.norm_real,abs_of_nonneg (Real.sqrt_nonneg _)]

theorem norm_base_le_one (z u : ℍ) : ‖base z u‖≤1 := by
  rw [norm_base]
  apply (div_le_one (norm_pos_iff.mpr (denominator_ne_zero z u))).mpr
  have hsq := Real.sq_sqrt (mul_nonneg z.im_pos.le u.im_pos.le)
  have hd := denominator_square z u
  nlinarith [sq_nonneg ‖(z:ℂ)-(u:ℂ)‖,norm_nonneg ((z:ℂ)-star (u:ℂ)),Real.sqrt_nonneg (z.im*u.im)]

theorem norm_base_lt_one {z u : ℍ} (hne : z≠u) : ‖base z u‖<1 := by
  rw [norm_base]
  apply (div_lt_one (norm_pos_iff.mpr (denominator_ne_zero z u))).mpr
  have hzu : (z:ℂ)-(u:ℂ)≠0 := sub_ne_zero.mpr (fun h => hne (UpperHalfPlane.coe_injective h))
  have hpos := sq_pos_of_pos (norm_pos_iff.mpr hzu)
  have hsq := Real.sq_sqrt (mul_nonneg z.im_pos.le u.im_pos.le)
  have hd := denominator_square z u
  nlinarith [norm_nonneg ((z:ℂ)-star (u:ℂ)),Real.sqrt_nonneg (z.im*u.im)]

theorem base_self (z : ℍ) : base z z=1 := by
  have hd : (z:ℂ)-star (z:ℂ)=2*Complex.I*(z.im:ℂ) := by
    apply Complex.ext <;> simp
    ring
  rw [base,Real.sqrt_mul_self z.im_pos.le,hd]
  exact div_self (by simpa only [hd] using denominator_ne_zero z z)

/-- Every nonreturning branch has exponential normalized-kernel decay. -/
theorem pow_tendsto_zero {z u : ℍ} (hne : z≠u) :
    Tendsto (fun k : ℕ => base z u^k) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_norm_lt_one (norm_base_lt_one hne)

/-- Bounded weight-dependent slash phases preserve this decay. -/
theorem bounded_phase_tendsto_zero {z u : ℍ} (hne : z≠u) (c : ℕ → ℂ)
    {C : ℝ} (hc : ∀ k,‖c k‖≤C) :
    Tendsto (fun k : ℕ => c k*base z u^k) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero (g:=fun k => C*‖base z u^k‖) (fun _ => norm_nonneg _) ?_ ?_
  · intro k
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hc k) (norm_nonneg _)
  · simpa using (pow_tendsto_zero hne).norm.const_mul C

/-- Nonreturning branch integrals are o(k) after restoring the Bergman
prefactor. This is the dominated-convergence step, allowing arbitrary
bounded measurable cell multipliers and weight-dependent slash phases. -/
theorem integral_tendsto_zero {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    (z u : α → ℍ) (c : ℕ → α → ℂ) (bound : α → ℝ)
    (hint : MeasureTheory.Integrable bound μ)
    (hmeas : ∀ k,MeasureTheory.AEStronglyMeasurable (fun x => c k x*base (z x) (u x)^k) μ)
    (hc : ∀ k,∀ᵐ x ∂μ,‖c k x‖≤bound x) (hne : ∀ᵐ x ∂μ,z x≠u x) :
    Tendsto (fun k : ℕ => ∫ x,c k x*base (z x) (u x)^k ∂μ) atTop (𝓝 0) := by
  have hbound : ∀ k,∀ᵐ x ∂μ,‖c k x*base (z x) (u x)^k‖≤bound x := by
    intro k
    filter_upwards [hc k] with x hx
    rw [norm_mul,norm_pow]
    exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (norm_base_le_one _ _))).trans hx
  have hlim : ∀ᵐ x ∂μ,Tendsto (fun k => c k x*base (z x) (u x)^k) atTop (𝓝 (0:ℂ)) := by
    filter_upwards [hne,MeasureTheory.ae_all_iff.mpr hc] with x hx hcx
    exact bounded_phase_tendsto_zero hx (fun k => c k x) hcx
  simpa using MeasureTheory.tendsto_integral_of_dominated_convergence
    bound hmeas hint hbound hlim

#print axioms integral_tendsto_zero
#print axioms pow_tendsto_zero
#print axioms bounded_phase_tendsto_zero

end AsymptoticBergmanDecay
