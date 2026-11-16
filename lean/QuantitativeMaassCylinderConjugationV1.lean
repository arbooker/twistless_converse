module

public import QuantitativeMaassCylinderBandsV1
public import QuantitativeMaassCylinderHilbertV1
public import QuantitativeMaassAllLevelAbelSpectralV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Literal radial integration on strip L2 has the spectral packet norm.
The whole-space cylinder identification discharges the quotient membership. -/
theorem cylinder_abel_ambient_norm (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (hr : ∀ q,star (F q)=F q)
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) :
    ‖(radialKernelData 0 (abelProfile F) (abelProfile_smooth F hF hc)
      R hR (abelProfile_support F _ hs)).operator‖≤‖coshWavePacket 0 F hF R hR hs‖ := by
  refine ContinuousLinearMap.opNorm_le_bound
    (radialKernelData 0 (abelProfile F) (abelProfile_smooth F hF hc)
      R hR (abelProfile_support F _ hs)).operator
    (norm_nonneg (coshWavePacket 0 F hF R hR hs)) ?_
  intro f
  have hf : f∈AutomorphicSpace 0 := by rw [cylinder_automorphicSpace_eq_top]; trivial
  have h := (coshWavePacket 0 F hF R hR hs).le_opNorm ⟨f,hf⟩
  conv at h => lhs; rw [←AllLevel.abelKernelOperator_eq_coshWavePacket 0 F hF hc hr R hR hs]
  exact h

def cylinderCappedRadialOperator (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    (ε : ℝ) (hε : 0<ε) (t : ℕ) :
    Lp ℂ 2 (quotientMeasure 0) →L[ℂ] Lp ℂ 2 (quotientMeasure 0) :=
  LogBands.boundedConjugation (quotientMeasure 0)
    (fun z => Real.log (cappedHeightWeight ε t z)) (cappedHeightWeight_log_measurable ε t)
    (radialKernelData 0 g hg R hR hs).operator ⌈(t:ℝ)*R+1⌉₊
    (cylinder_radial_band_propagation g hg R hR hs hε t _ (Nat.le_ceil _))

/-- On the dense finite-band domain this is literal multiplication by the
weight, radial integration, and multiplication by the inverse weight. -/
theorem cylinderCappedRadialOperator_coeFn (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    (ε : ℝ) (hε : 0<ε) (t : ℕ)
    (f : LogBands.finiteBandSpace (quotientMeasure 0)
      (fun z => Real.log (cappedHeightWeight ε t z)) (cappedHeightWeight_log_measurable ε t)) :
    cylinderCappedRadialOperator g hg R hR hs ε hε t f.val=ᵐ[quotientMeasure 0]
      (fun z => (cappedHeightWeight ε t z:ℂ)*
        ((radialKernelData 0 g hg R hR hs).operator
          (LogBands.exponentialEnd (quotientMeasure 0)
            (fun z => Real.log (cappedHeightWeight ε t z)) (cappedHeightWeight_log_measurable ε t)
            (-1) f).val) z) := by
  have hh := LogBands.boundedConjugation_coeFn (quotientMeasure 0)
    (fun z => Real.log (cappedHeightWeight ε t z)) (cappedHeightWeight_log_measurable ε t)
    (radialKernelData 0 g hg R hR hs).operator ⌈(t:ℝ)*R+1⌉₊
    (cylinder_radial_band_propagation g hg R hR hs hε t _ (Nat.le_ceil _)) f
  simpa only [Real.exp_log (cappedHeightWeight_pos hε t _)] using! hh

theorem cylinderCappedRadialOperator_norm (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    (ε : ℝ) (hε : 0<ε) (t : ℕ) :
    ‖cylinderCappedRadialOperator g hg R hR hs ε hε t‖≤
      5*(1+(t:ℝ)*R)*Real.exp ((t:ℝ)*R+3)*‖(radialKernelData 0 g hg R hR hs).operator‖ := by
  have h := LogBands.boundedConjugation_norm_bound (quotientMeasure 0)
    (fun z => Real.log (cappedHeightWeight ε t z)) (cappedHeightWeight_log_measurable ε t)
    (radialKernelData 0 g hg R hR hs).operator ⌈(t:ℝ)*R+1⌉₊
    (cylinder_radial_band_propagation g hg R hR hs hε t _ (Nat.le_ceil _))
  apply h.trans
  have hc : (⌈(t:ℝ)*R+1⌉₊:ℝ)<(t:ℝ)*R+2 := by
    have hceil := Nat.ceil_lt_add_one (show 0≤(t:ℝ)*R+1 by positivity)
    linarith
  have htR : 0≤(t:ℝ)*R := mul_nonneg (Nat.cast_nonneg t) hR
  have hm : ((2*⌈(t:ℝ)*R+1⌉₊+1:ℕ):ℝ)≤5*(1+(t:ℝ)*R) := by
    push_cast
    linarith
  have he : Real.exp ((⌈(t:ℝ)*R+1⌉₊:ℝ)+1)≤Real.exp ((t:ℝ)*R+3) :=
    Real.exp_le_exp.mpr (by linarith)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hm he (Real.exp_pos _).le (by positivity)) (norm_nonneg _)

/-- The actual capped cylinder operator has a spectral, rather than a
Schur-mass, bound; the constant is uniform in the cutoff height ε. -/
theorem cylinderCappedAbelOperator_spectral_norm (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (hr : ∀ q,star (F q)=F q)
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R))
    (ε : ℝ) (hε : 0<ε) (t : ℕ) :
    ‖cylinderCappedRadialOperator (abelProfile F) (abelProfile_smooth F hF hc)
      R hR (abelProfile_support F _ hs) ε hε t‖≤
      5*(1+(t:ℝ)*R)*Real.exp ((t:ℝ)*R+3)*‖coshWavePacket 0 F hF R hR hs‖ :=
  (cylinderCappedRadialOperator_norm _ _ R hR _ ε hε t).trans
    (mul_le_mul_of_nonneg_left (cylinder_abel_ambient_norm F hF hc hr R hR hs) (by positivity))

#print axioms cylinder_abel_ambient_norm
#print axioms cylinderCappedRadialOperator_coeFn
#print axioms cylinderCappedRadialOperator_norm
#print axioms cylinderCappedAbelOperator_spectral_norm

end QuantitativeMaass
