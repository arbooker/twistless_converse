module

public import AsymptoticCylinderV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCylinder

open MeasureTheory Set Filter AsymptoticFourierNorm
open scoped InnerProduct

noncomputable def weight (ε : ℝ) (z : Cylinder) : ℂ := (min (z.2/ε) 1:ℝ)

theorem weight_measurable (ε : ℝ) : AEStronglyMeasurable (weight ε) measure := by
  have h : Continuous (weight ε) := by unfold weight; fun_prop
  exact h.aestronglyMeasurable

theorem weight_bound {ε : ℝ} (hε : 0<ε) : ∀ᵐ z ∂measure,‖weight ε z‖≤1 := by
  filter_upwards [height_positive] with z hz
  have h0 : 0≤min (z.2/ε) 1 := le_min (div_nonneg hz.le hε.le) zero_le_one
  simp [weight,abs_of_nonneg h0]

/-- In the fixed ambient realization, inclusion from weight t to weight
t+1 is multiplication by this single capped height factor. -/
noncomputable def inclusion {ε : ℝ} (hε : 0<ε) : Space →L[ℂ] Space :=
  AsymptoticL2Multiplier.operator (weight ε) (weight_measurable ε) (weight_bound hε)

theorem inclusion_coeFn {ε : ℝ} (hε : 0<ε) (f : Space) :
    inclusion hε f =ᵐ[measure] (fun z => weight ε z*f z) :=
  AsymptoticL2Multiplier.operator_coeFn _ _ _ f

theorem inclusion_norm_le {ε : ℝ} (hε : 0<ε) : ‖inclusion hε‖≤1 :=
  AsymptoticL2Multiplier.operator_norm_le _ _ (by norm_num) _

theorem inclusion_adjoint {ε : ℝ} (hε : 0<ε) : (inclusion hε).adjoint=inclusion hε :=
  AsymptoticL2Multiplier.operator_adjoint _ _ _ (Filter.Eventually.of_forall (fun _ => by simp [weight]))

theorem weighted_mode_norm_sq (m t n : ℕ) {scale ε : ℝ} (hε : 0<ε)
    {z : Cylinder} (hz : 0≤z.2) :
    ‖weight ε z*mode m t n scale ε z‖^2=density m (t+1) (scale*(n+1:ℕ)) ε z.2 := by
  rw [norm_mul,mul_pow,mode_norm_sq m t n scale hε hz]
  have h0 : 0≤min (z.2/ε) 1 := le_min (div_nonneg hz hε.le) zero_le_one
  simp only [weight,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg h0,density,
    Nat.mul_add,Nat.mul_one,pow_add]
  ring

theorem inclusion_mode_norm_sq (m t n : ℕ) {scale ε : ℝ} (hs : 0<scale) (hε : 0<ε) :
    ‖inclusion hε (modeLp m t n hs hε)‖^2=beta m (t+1) (scale*(n+1:ℕ)) ε := by
  rw [AsymptoticL2Multiplier.norm_sq_eq_integral]
  have he : (∫ z,‖inclusion hε (modeLp m t n hs hε) z‖^2 ∂measure)=
      ∫ z,‖modeLp m (t+1) n hs hε z‖^2 ∂measure := by
    apply integral_congr_ae
    filter_upwards [inclusion_coeFn hε (modeLp m t n hs hε),
      modeLp_coeFn m t n hs hε,modeLp_coeFn m (t+1) n hs hε,height_positive] with z hw ht ht' hz
    rw [hw,ht,ht',weighted_mode_norm_sq m t n hε hz.le,mode_norm_sq m (t+1) n scale hε hz.le]
  rw [he,← AsymptoticL2Multiplier.norm_sq_eq_integral,modeLp_norm_sq]

noncomputable def unitMode (m t n : ℕ) {scale ε : ℝ} (hs : 0<scale) (hε : 0<ε) : Space :=
  (Real.sqrt (beta m t (scale*(n+1:ℕ)) ε):ℂ)⁻¹ • modeLp m t n hs hε

theorem unitMode_norm_sq (m t n : ℕ) {scale ε : ℝ} (hs : 0<scale) (hε : 0<ε) :
    ‖unitMode m t n hs hε‖^2=1 := by
  simp only [unitMode,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,inv_pow,
    Real.sq_sqrt (beta_nonneg m t hε),modeLp_norm_sq]
  exact inv_mul_cancel₀ (beta_pos m t (mul_pos hs (by positivity)) hε).ne'

/-- This is the weighted adjoint-pairing estimate in the paper, as an
identity for the concrete cylinder inclusion and normalized Fourier modes. -/
theorem inclusion_adjoint_unitMode_norm_sq (m t n : ℕ) {scale ε : ℝ}
    (hs : 0<scale) (hε : 0<ε) :
    ‖(inclusion hε).adjoint (unitMode m t n hs hε)‖^2=
      beta m (t+1) (scale*(n+1:ℕ)) ε / beta m t (scale*(n+1:ℕ)) ε := by
  rw [inclusion_adjoint]
  simp only [unitMode,map_smul,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,inv_pow,
    Real.sq_sqrt (beta_nonneg m t hε),inclusion_mode_norm_sq]
  rw [div_eq_mul_inv,mul_comm]

#print axioms inclusion_adjoint_unitMode_norm_sq

end AsymptoticCylinder
