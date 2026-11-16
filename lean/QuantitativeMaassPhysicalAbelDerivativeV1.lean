module

public import QuantitativeMaassPhysicalAbelSmoothV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Ordinary and physical derivatives agree locally at every interior point. -/
theorem physical_derivative_eventually (F : ℝ → ℂ) (q : ℝ) (hq : 1<q) :
    derivWithin F (Ici 1)=ᶠ[𝓝 q] deriv F := by
  filter_upwards [Ioi_mem_nhds hq] with x hx
  exact derivWithin_of_mem_nhds (Ici_mem_nhds hx)

/-- Differentiate the literal horizontal Abel profile, including its center.
Only smoothness on the physical half-line is required. -/
theorem abelProfile_horizontal_hasDerivAt (F : ℝ → ℂ)
    (hF : ContDiffOn ℝ ∞ F (Ici 1)) (B : ℝ) (hB : 1≤B)
    (hs : Function.support F⊆Iic B) (v : ℝ) :
    HasDerivAt (parabolicLineProfile (abelProfile F) 1)
      (v • parabolicLineProfile (abelProfile (deriv F)) 1 v) v := by
  have hF₁ : ContDiffOn ℝ ∞ (derivWithin F (Ici 1)) (Ici 1) := hF.derivWithin (uniqueDiffOn_Ici (1:ℝ)) (by simp)
  have hh := (physicalQuadraticMean_hasDerivAt (derivWithin F (Ici 1)) hF₁ (B+1) v).const_mul
    (-(Real.sqrt 2/Real.pi:ℂ))
  have he : parabolicLineProfile (abelProfile F) 1=(fun x =>
      -(Real.sqrt 2/Real.pi:ℂ)*physicalQuadraticMean (derivWithin F (Ici 1)) (B+1) x) :=
    funext (abelProfile_horizontal_mean F B hB hs)
  rw [← he] at hh
  have hd : Function.support (deriv F)⊆Iic B :=
    support_deriv_subset.trans (closure_minimal hs isClosed_Iic)
  have hmean : physicalQuadraticMean (derivWithin (derivWithin F (Ici 1)) (Ici 1)) (B+1) v=
      physicalQuadraticMean (derivWithin (deriv F) (Ici 1)) (B+1) v := by
    unfold physicalQuadraticMean
    simp only [integral_Icc_eq_integral_Ioc]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs0
    have hq : 1<1+v^2/2+s^2 := by nlinarith [sq_nonneg v,sq_pos_of_pos hs0.1]
    exact (physical_derivative_eventually F _ hq).derivWithin_eq_of_nhds
  rw [hmean] at hh
  rw [abelProfile_horizontal_mean (deriv F) B hB hd v]
  convert hh using 1
  simp only [Complex.real_smul]
  ring

/-- Differentiation of the actual one-sided Abel integral at every interior
physical radial coordinate; no extension to q<1 is supplied. -/
theorem abelProfile_hasDerivAt_physical (F : ℝ → ℂ)
    (hF : ContDiffOn ℝ ∞ F (Ici 1)) (B : ℝ) (hB : 1≤B)
    (hs : Function.support F⊆Iic B) (q : ℝ) (hq : 1<q) :
    HasDerivAt (abelProfile F) (abelProfile (deriv F) q) q := by
  let v := Real.sqrt (2*(q-1))
  have hv : 0<v := Real.sqrt_pos.mpr (by linarith)
  have hv2 : v^2=2*(q-1) := Real.sq_sqrt (by linarith)
  have hd := (((hasDerivAt_id q).sub_const 1).const_mul 2).sqrt (by linarith : 2*(q-1)≠0)
  simp only [id_eq,mul_one] at hd
  have hh := (abelProfile_horizontal_hasDerivAt F hF B hB hs v).scomp q hd
  have he : (fun x => parabolicLineProfile (abelProfile F) 1 (Real.sqrt (2*(x-1))))=ᶠ[𝓝 q]
      abelProfile F := by
    filter_upwards [Ioi_mem_nhds hq] with x hx
    change 1<x at hx
    unfold parabolicLineProfile
    rw [Real.sq_sqrt (by linarith : 0≤2*(x-1))]
    congr 1
    ring
  have hvalue : parabolicLineProfile (abelProfile (deriv F)) 1 v=abelProfile (deriv F) q := by
    unfold parabolicLineProfile
    rw [hv2]
    congr 1
    ring
  simp only [Function.comp_def] at hh
  rw [show Real.sqrt (2*(q-1))=v from rfl,hvalue,smul_smul] at hh
  have hc : 2/(2*v)*v=1 := by field_simp
  rw [hc,one_smul] at hh
  exact hh.congr_of_eventuallyEq he.symm

#print axioms physical_derivative_eventually
#print axioms abelProfile_horizontal_hasDerivAt
#print axioms abelProfile_hasDerivAt_physical

end QuantitativeMaass
