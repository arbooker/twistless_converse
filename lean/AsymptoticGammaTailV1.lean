module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public section

namespace AsymptoticGammaTail

open MeasureTheory Set Filter
open scoped Topology

/-- The polynomial-exponential density underlying the Fourier norm. -/
noncomputable def kernel (m : ℕ) (r y : ℝ) : ℝ := y^m*Real.exp (-(r*y))

/-- Its integral, in the integer-exponent normalization needed here. -/
theorem integral_kernel (m : ℕ) {r : ℝ} (hr : 0<r) :
    (∫ y in Ioi 0,kernel m r y)=(1/r)^(m+1)*(m.factorial:ℝ) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a:=(m:ℝ)+1) (by positivity) hr
  simpa only [kernel,add_sub_cancel_right,Real.Gamma_nat_eq_factorial,
    Real.rpow_add (by positivity : (0:ℝ)<1/r),Real.rpow_one,Real.rpow_natCast,pow_succ] using h

theorem kernel_nonneg (m : ℕ) (r : ℝ) {y : ℝ} (hy : 0≤y) : 0≤kernel m r y := by
  dsimp [kernel]
  positivity

theorem integrable_kernel (m : ℕ) {r : ℝ} (hr : 0<r) :
    Integrable (kernel m r) (volume.restrict (Ioi 0)) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_kernel m hr]
  positivity

/-- Multiplication by the height increments the gamma exponent. -/
theorem height_mul_kernel (m : ℕ) (r y : ℝ) : y*kernel m r y=kernel (m+1) r y := by
  simp only [kernel,pow_succ]
  ring

/-- Markov's argument in integral form, requiring only the first moment.
This statement also applies to other nonnegative densities. -/
theorem half_mass_below {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (x g : α → ℝ) {ε : ℝ} (hε : 0<ε) (hx : Measurable x)
    (hg : Integrable g μ) (hg0 : 0≤ᵐ[μ] g)
    (hxg : Integrable (fun y => x y*g y) μ) (hxg0 : 0≤ᵐ[μ] (fun y => x y*g y))
    (hmoment : 2*(∫ y,x y*g y ∂μ)≤ε*(∫ y,g y ∂μ)) :
    (∫ y,g y ∂μ)/2≤∫ y in {y | x y≤ε},g y ∂μ := by
  let s : Set α := {y | x y≤ε}
  have hs : MeasurableSet s := hx measurableSet_Iic
  have htail : ε*(∫ y in sᶜ,g y ∂μ)≤∫ y,x y*g y ∂μ := by
    calc
      ε*(∫ y in sᶜ,g y ∂μ) = ∫ y in sᶜ,ε*g y ∂μ := (integral_const_mul _ _).symm
      _ ≤ ∫ y in sᶜ,x y*g y ∂μ := by
        apply integral_mono_ae ((hg.restrict).const_mul ε) hxg.restrict
        filter_upwards [ae_restrict_mem hs.compl,hg0.filter_mono (ae_mono Measure.restrict_le_self)] with y hy hgy
        have hy' : ε<x y := lt_of_not_ge hy
        exact mul_le_mul_of_nonneg_right hy'.le hgy
      _ ≤ _ := setIntegral_le_integral hxg hxg0
  have hsplit := integral_add_compl hs hg
  have hmain : ε*((∫ y,g y ∂μ)/2-(∫ y in s,g y ∂μ))≤0 := by nlinarith
  have hh : (∫ y,g y ∂μ)/2-(∫ y in s,g y ∂μ)≤0 := by nlinarith
  exact sub_nonpos.mp hh

/-- At twice the mean, at least half of a gamma integral is retained. -/
theorem half_kernel_below (m : ℕ) {r ε : ℝ} (hr : 0<r) (hε : 0<ε)
    (hthreshold : 2*((m:ℝ)+1)≤r*ε) :
    ((1/r)^(m+1)*(m.factorial:ℝ))/2 ≤
      ∫ y in Iic ε,kernel m r y ∂(volume.restrict (Ioi 0)) := by
  have hg := integrable_kernel m hr
  have hg0 : 0≤ᵐ[volume.restrict (Ioi 0)] kernel m r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact kernel_nonneg m r hy.le
  have hxg : Integrable (fun y => y*kernel m r y) (volume.restrict (Ioi 0)) := by
    simpa only [height_mul_kernel] using integrable_kernel (m+1) hr
  have hxg0 : 0≤ᵐ[volume.restrict (Ioi 0)] (fun y => y*kernel m r y) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi,hg0] with y hy hgy
    exact mul_nonneg hy.le hgy
  have hm : 2*(∫ y in Ioi 0,y*kernel m r y)≤ε*(∫ y in Ioi 0,kernel m r y) := by
    simp_rw [height_mul_kernel]
    rw [integral_kernel (m+1) hr,integral_kernel m hr,Nat.factorial_succ]
    push_cast
    have hh := mul_le_mul_of_nonneg_right hthreshold
      (by positivity : 0≤(1/r)^(m+1)*(m.factorial:ℝ)/r)
    convert hh using 1 <;> simp only [pow_succ] <;> field_simp
  have h := half_mass_below (fun y : ℝ => y) (kernel m r) hε measurable_id hg hg0 hxg hxg0 hm
  rwa [integral_kernel m hr] at h

#print axioms half_kernel_below

end AsymptoticGammaTail
