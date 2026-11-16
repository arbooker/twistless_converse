module

public import QuantitativeMaassAbelFluxV1
public import QuantitativeMaassShiftedWavePacketV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem abelProfile_deriv (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    deriv (abelProfile F)=abelProfile (deriv F) := by
  funext q
  exact ((abelIntegral_hasDerivAt (deriv F) (contDiff_infty_iff_deriv.mp hF).2
    hc.deriv q).const_mul (-(Real.sqrt 2/Real.pi:ℂ))).deriv

/-- Second time derivative expressed in the coordinate v=cosh t. -/
def coshTimeOperator (F : ℝ → ℂ) (v : ℝ) : ℂ :=
  ((v:ℂ)^2-1)*deriv (deriv F) v+(v:ℂ)*deriv F v

theorem coshTimeOperator_smooth (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (coshTimeOperator F) := by
  have hF' := (contDiff_infty_iff_deriv.mp hF).2
  have hF'' := (contDiff_infty_iff_deriv.mp hF').2
  have hz : ContDiff ℝ ∞ (fun v : ℝ => (v:ℂ)) := Complex.ofRealCLM.contDiff
  unfold coshTimeOperator
  fun_prop

theorem coshTimeOperator_compact (F : ℝ → ℂ) (hc : HasCompactSupport F) :
    HasCompactSupport (coshTimeOperator F) :=
  hc.deriv.deriv.mul_left.add hc.deriv.mul_left

theorem coshTimeOperator_deriv (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) :
    deriv (coshTimeOperator F)=abelAuxOperator (deriv F) := by
  have hF' := (contDiff_infty_iff_deriv.mp hF).2
  have hF'' := (contDiff_infty_iff_deriv.mp hF').2
  funext v
  have hz := (hasDerivAt_id v).ofReal_comp
  have hd := (((hz.pow 2).sub_const 1).mul
    ((hF''.differentiable (by simp)) v).hasDerivAt).add
      (hz.mul ((hF'.differentiable (by simp)) v).hasDerivAt)
  convert hd.deriv using 1
  · rfl
  · simp only [abelAuxOperator,Pi.pow_apply,id_eq,Complex.ofReal_one,
      Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul]
    ring

/-- Exact differential intertwining of the constructed Abel transform:
the shifted hyperbolic radial Laplacian is minus the time second derivative. -/
theorem abelProfile_laplacian (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (q : ℝ) :
    radialLaplacianProfile (abelProfile F) q=
      (1/4:ℂ)*abelProfile F q-abelProfile (coshTimeOperator F) q := by
  have hF' := (contDiff_infty_iff_deriv.mp hF).2
  unfold radialLaplacianProfile
  rw [abelProfile_deriv F hF hc,abelProfile_deriv (deriv F) hF' hc.deriv]
  simp only [abelProfile,coshTimeOperator_deriv F hF,
    abelIntegral_auxOperator (deriv F) hF' hc.deriv]
  ring

/-- The differential identity on actual upper-half-plane kernel columns. -/
theorem abelRadial_laplacian (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (w z : UpperHalfPlane) :
    upperLaplacian (radialFunction (abelProfile F) w) z=
      (1/4:ℂ)*abelProfile F (Real.cosh (dist z w))-
        abelProfile (coshTimeOperator F) (Real.cosh (dist z w)) := by
  rw [radialFunction_laplacian _ (abelProfile_smooth F hF hc),abelProfile_laplacian F hF hc]

def coshTimeTest (F : ℝ → ℂ) (t : ℝ) : ℂ := F (Real.cosh t)

theorem coshTimeTest_second (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (t : ℝ) :
    deriv (deriv (coshTimeTest F)) t=coshTimeOperator F (Real.cosh t) := by
  have h := radial_second_comp F hF Real.cosh Real.sinh (Real.cosh t) t
    (Eventually.of_forall Real.hasDerivAt_cosh) (Real.hasDerivAt_sinh t)
  change deriv (deriv (fun u => F (Real.cosh u))) t=_
  rw [h]
  have hs : (Real.sinh t:ℂ)^2=(Real.cosh t:ℂ)^2-1 := by
    exact_mod_cast Real.sinh_sq t
  simp only [coshTimeOperator,hs]

theorem coshTimeTest_support (F : ℝ → ℂ) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    Function.support (coshTimeTest F)⊆Icc (-R) R := by
  intro t ht
  have hh := Real.cosh_le_cosh.mp (hs ht)
  rw [abs_of_nonneg hR] at hh
  exact abs_le.mp hh

/-- The same compact time test defines the already constructed spectral
wave packet. Equality with the Abel integral operator is a remaining step. -/
theorem coshTimeTest_waveWeight (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) :
    Wave.ShiftedWaveWeight (coshTimeTest F) := by
  have hc : HasCompactSupport (coshTimeTest F) :=
    (isCompact_Icc : IsCompact (Icc (-R) R)).of_isClosed_subset isClosed_closure
      (closure_minimal (coshTimeTest_support F R hR hs) isClosed_Icc)
  exact Wave.shiftedWaveWeight_of_support
    ((hF.continuous.comp Real.continuous_cosh).integrable_of_hasCompactSupport hc)
    hR (coshTimeTest_support F R hR hs)

#print axioms abelProfile_laplacian
#print axioms abelRadial_laplacian
#print axioms coshTimeTest_second
#print axioms coshTimeTest_waveWeight

end QuantitativeMaass
