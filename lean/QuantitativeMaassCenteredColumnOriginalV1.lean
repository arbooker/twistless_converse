module

public import QuantitativeMaassCylinderCenteredCappedV1
public import QuantitativeMaassCappedColumnOriginalV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped Topology ContDiff SchwartzMap

namespace QuantitativeMaass

/-- The capped original Euler wave has zero mean on a unit horizontal
interval starting at any real coordinate. -/
theorem cappedEuler_vadd_mean_zero {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ : ℕ) (ε : ℝ) (t : ℕ) (z : ℍ) :
    (∫ y in Icc (0:ℝ) 1,(cappedHeightWeight ε t (y+ᵥz):ℂ)*
      principalEulerPhysical b r σ (y+ᵥz))=0 := by
  have he (y : ℝ) : (cappedHeightWeight ε t (y+ᵥz):ℂ)*
      principalEulerPhysical b r σ (y+ᵥz)=
      (cappedHeightWeight ε t z:ℂ)*principalEulerWave b r σ (y+z.re,z.im) := by
    simp only [cappedHeightWeight,principalEulerPhysical,coe_re,coe_im,vadd_re,vadd_im]
  simp_rw [he]
  rw [integral_const_mul,integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_add_right
      (fun x : ℝ => principalEulerWave b r σ (x,z.im)) z.re]
  have hh := (principalEulerWave_periodic b r σ z.im).intervalIntegral_add_eq z.re 0
  simp only [zero_add] at hh
  rw [show (0:ℝ)+z.re=z.re from zero_add _,
    show (1:ℝ)+z.re=z.re+1 from add_comm _ _,hh,
    intervalIntegral.integral_of_le zero_le_one,principalEulerWave_mean_zero hb r σ z.im z.im_pos,
    mul_zero]

/-- The finite-band capped column remains continuous along each horizontal
curve because the weight and the chosen row are constant along that curve. -/
theorem cylinderCappedTimeColumn_vadd_continuous (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ → ℂ)) (he : Function.Even f)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (ε : ℝ) (t : ℕ) (z : ℍ) :
    Continuous (fun y : ℝ => cylinderCappedTimeColumn f (f.smooth ⊤) he hc R hR
      (evenCoshLift_support_of_time_support f R hR hs) ε t (y+ᵥz)) := by
  let S := (LogBands.rowInverseSum (quotientMeasure 0)
    (fun w => Real.log (cappedHeightWeight ε t w))
    (cappedHeightWeight_log_measurable ε t)
    ⌈(t:ℝ)*R+1⌉₊ ⌊Real.log (cappedHeightWeight ε t z)⌋).adjoint
  have hcol := (cylinderAbelColumn_continuous (evenCoshLift f)
    (evenCoshLift_smoothOn f (f.smooth ⊤) he hc) R hR
    (evenCoshLift_support_of_time_support f R hR hs)).comp (cylinder_vadd_continuous z)
  have hh := S.continuous.comp
    (hcol.const_smul ((Real.exp (Real.log (cappedHeightWeight ε t z))):ℂ))
  simpa only [S,cylinderCappedTimeColumn,LogBands.conjugatedColumn,
    cappedHeightWeight,vadd_im,Function.comp_def,Pi.smul_apply] using hh

/-- Removing the horizontal mean leaves the exact original Euler scalar
action unchanged, now for the constructed finite-energy centered column. -/
theorem cylinderCenteredCappedColumn_original {N Q : ℕ} {hQ : 0<Q}
    (hN : 0<N) (A : FinitenessCertificate.Certificate N Q hQ)
    (P : FinitenessGlobalHeight.Parameters A) (r : ℝ) (σ : ℕ) {b : ℕ → ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (hr : ∀ s,star (f s)=f s)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) (z : ℍ) :
    inner ℂ (cylinderCenteredCappedColumn f hc he R hR hs P.ε (P.s+3) z)
      (principalEulerCylinderLp hN A P r σ hb)=
      cosinePacket f r *
        ((cappedHeightWeight P.ε (P.s+3) z:ℂ)*principalEulerPhysical b r σ z) := by
  let c := cylinderCappedTimeColumn f (f.smooth ⊤) he hc R hR
    (evenCoshLift_support_of_time_support f R hR hs) P.ε (P.s+3)
  let v := principalEulerCylinderLp hN A P r σ hb
  have hi : IntegrableOn (fun y : ℝ => c (y+ᵥz)) (Icc (0:ℝ) 1) volume :=
    (cylinderCappedTimeColumn_vadd_continuous f hc he R hR hs P.ε (P.s+3) z).integrableOn_Icc
  have hm : inner ℂ (∫ y in Icc (0:ℝ) 1,c (y+ᵥz)) v=0 := by
    rw [←inner_conj_symm (∫ y in Icc (0:ℝ) 1,c (y+ᵥz)) v,
      ←integral_inner hi v,←integral_conj]
    simp only [inner_conj_symm]
    simp_rw [show ∀ w,inner ℂ (c w) v=cosinePacket f r*
      ((cappedHeightWeight P.ε (P.s+3) w:ℂ)*principalEulerPhysical b r σ w) from
      fun w => cylinderCappedTimeColumn_original hN A P r σ hb f (f.smooth ⊤) he hc hr R hR hs w]
    rw [integral_const_mul,cappedEuler_vadd_mean_zero hb.polynomialGrowth,mul_zero]
  rw [cylinderCenteredCappedColumn_eq,inner_sub_left]
  change inner ℂ (c z) v-inner ℂ (∫ y in Icc (0:ℝ) 1,c (y+ᵥz)) v=_
  rw [hm,sub_zero]
  exact cylinderCappedTimeColumn_original hN A P r σ hb f (f.smooth ⊤) he hc hr R hR hs z

#print axioms cappedEuler_vadd_mean_zero
#print axioms cylinderCappedTimeColumn_vadd_continuous
#print axioms cylinderCenteredCappedColumn_original

end QuantitativeMaass
