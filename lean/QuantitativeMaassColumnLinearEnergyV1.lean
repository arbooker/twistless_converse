module

public import QuantitativeMaassWindowColumnSplittingV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass

/-- The spectral residual is linear on the actual Schwartz time profiles. -/
theorem spectralResidualSchwartz_linear (t : ℝ) (f g : SchwartzMap ℝ ℂ) (a b : ℂ) :
    spectralResidualSchwartz t (a • f+b • g)=
      a • spectralResidualSchwartz t f+b • spectralResidualSchwartz t g := by
  simp only [spectralResidualSchwartz,map_add,map_smul,smul_add]
  module

/-- A linear decomposition of time profiles gives an integrated column
energy bound on every compact center region. -/
theorem cylinderTimeColumn_linear_energy (f g h : SchwartzMap ℝ ℂ)
    (hfc : HasCompactSupport (f:ℝ→ℂ)) (hgc : HasCompactSupport (g:ℝ→ℂ))
    (hhc : HasCompactSupport (h:ℝ→ℂ))
    (hfe : Function.Even f) (hge : Function.Even g) (hhe : Function.Even h)
    (R : ℝ) (hR : 0≤R) (hsf : Function.support f⊆Icc (-R) R)
    (hsg : Function.support g⊆Icc (-R) R) (hsh : Function.support h⊆Icc (-R) R)
    (a b : ℂ) (hlin : h=a • f+b • g) (S : Set ℍ) (hS : IsCompact S) :
    (∫ z in S,‖cylinderTimeColumn h hhc hhe R hR hsh z‖^2)≤
      2*‖a‖^2*(∫ z in S,‖cylinderTimeColumn f hfc hfe R hR hsf z‖^2)+
      2*‖b‖^2*(∫ z in S,‖cylinderTimeColumn g hgc hge R hR hsg z‖^2) := by
  let x := cylinderTimeColumn f hfc hfe R hR hsf
  let y := cylinderTimeColumn g hgc hge R hR hsg
  let z := cylinderTimeColumn h hhc hhe R hR hsh
  have hx : Continuous x := cylinderAbelColumn_continuous _ _ _ _ _
  have hy : Continuous y := cylinderAbelColumn_continuous _ _ _ _ _
  have hz : Continuous z := cylinderAbelColumn_continuous _ _ _ _ _
  have hxi : IntegrableOn (fun u => ‖x u‖^2) S := (hx.norm.pow 2).continuousOn.integrableOn_compact hS
  have hyi : IntegrableOn (fun u => ‖y u‖^2) S := (hy.norm.pow 2).continuousOn.integrableOn_compact hS
  have hzi : IntegrableOn (fun u => ‖z u‖^2) S := (hz.norm.pow 2).continuousOn.integrableOn_compact hS
  have hp (u : ℍ) : ‖z u‖^2≤2*‖a‖^2*‖x u‖^2+2*‖b‖^2*‖y u‖^2 := by
    have heq : z u=a • x u+b • y u := by
      apply cylinderAutomorphic.injective
      simpa only [map_add,map_smul] using
        cylinderTimeColumn_linear f g h hfc hgc hhc hfe hge hhe R hR hsf hsg hsh a b hlin u
    have hn := norm_add_le (a • x u) (b • y u)
    rw [←heq,norm_smul,norm_smul] at hn
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
    nlinarith [sq_nonneg (‖a‖*‖x u‖-‖b‖*‖y u‖)]
  have hh := integral_mono_ae hzi ((hxi.const_mul (2*‖a‖^2)).add (hyi.const_mul (2*‖b‖^2)))
    (Eventually.of_forall hp)
  simp only [Pi.add_apply] at hh
  rw [integral_add (hxi.const_mul (2*‖a‖^2)) (hyi.const_mul (2*‖b‖^2)),
    integral_const_mul,integral_const_mul] at hh
  exact hh

#print axioms spectralResidualSchwartz_linear
#print axioms cylinderTimeColumn_linear_energy
end QuantitativeMaass
