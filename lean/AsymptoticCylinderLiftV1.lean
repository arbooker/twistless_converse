module

public import AsymptoticFlatHyperbolicV1
public import AsymptoticZeroExtensionV1
public import AsymptoticCylinderEmbeddingV1
public import AsymptoticWeightedBranchesV1

set_option autoImplicit false
set_option maxHeartbeats 400000
@[expose] public section

namespace AsymptoticCylinderLift

open MeasureTheory UpperHalfPlane Set Filter
open AsymptoticStripCoordinates AsymptoticFlatHyperbolic

noncomputable def pullback : AsymptoticCylinder.Space →ₗᵢ[ℂ] Lp ℂ 2 flatStrip :=
  Lp.compMeasurePreservingₗᵢ ℂ cylinder cylinder_preserving

/-- The cylinder realization as a strip-supported section in hyperbolic
L². The map includes the exact height factor and preserves the norm. -/
noncomputable def lift : AsymptoticCylinder.Space →ₗᵢ[ℂ] AsymptoticHyperbolicSlash.Space :=
  heightMap.comp ((AsymptoticZeroExtension.isometry flat AsymptoticMassTransport.strip
    AsymptoticMassTransport.strip_measurable).comp pullback)

theorem lift_coeFn (f : AsymptoticCylinder.Space) :
    lift f =ᵐ[volume] AsymptoticMassTransport.strip.indicator
      (fun z : ℍ => (z.im:ℂ)*f (cylinder z)) := by
  have hp := (ae_eq_restrict_iff_indicator_ae_eq AsymptoticMassTransport.strip_measurable).mp
    (Lp.coeFn_compMeasurePreserving f cylinder_preserving)
  have hz := AsymptoticZeroExtension.isometry_coeFn flat AsymptoticMassTransport.strip
    AsymptoticMassTransport.strip_measurable (pullback f)
  have hh := heightMap_coeFn (AsymptoticZeroExtension.isometry flat AsymptoticMassTransport.strip
    AsymptoticMassTransport.strip_measurable (pullback f))
  filter_upwards [hh,hyperbolic_ac_flat.ae_eq hz,hyperbolic_ac_flat.ae_eq hp] with z hheight hzero hperiod
  change heightMap (AsymptoticZeroExtension.isometry flat AsymptoticMassTransport.strip
    AsymptoticMassTransport.strip_measurable (pullback f)) z=_
  rw [hheight,hzero]
  change (z.im:ℂ)*AsymptoticMassTransport.strip.indicator (pullback f) z=_
  change AsymptoticMassTransport.strip.indicator (pullback f) z=
    AsymptoticMassTransport.strip.indicator (fun w => f (cylinder w)) z at hperiod
  rw [hperiod]
  classical
  by_cases hzs : z∈AsymptoticMassTransport.strip <;> simp [hzs]

theorem lift_coeFn_of_ae (f : AsymptoticCylinder.Space)
    (φ : AsymptoticCylinder.Cylinder → ℂ) (hφ : f =ᵐ[AsymptoticCylinder.measure] φ) :
    lift f =ᵐ[volume] AsymptoticMassTransport.strip.indicator
      (fun z : ℍ => (z.im:ℂ)*φ (cylinder z)) := by
  have hp₀ : ∀ᵐ z ∂flatStrip,f (cylinder z)=φ (cylinder z) :=
    cylinder_preserving.quasiMeasurePreserving.ae hφ
  have hp := (ae_eq_restrict_iff_indicator_ae_eq AsymptoticMassTransport.strip_measurable).mp hp₀
  filter_upwards [lift_coeFn f,hyperbolic_ac_flat.ae_eq hp] with z hz he
  rw [hz]
  classical
  by_cases hs : z∈AsymptoticMassTransport.strip
  · simp only [Set.indicator_of_mem hs] at he ⊢
    rw [he]
  · simp [hs]

theorem lift_norm (f : AsymptoticCylinder.Space) : ‖lift f‖=‖f‖ := lift.norm_map f

theorem lift_zero_off_strip (f : AsymptoticCylinder.Space) :
    ∀ᵐ z ∂volume,z∉AsymptoticMassTransport.strip → lift f z=0 := by
  filter_upwards [lift_coeFn f] with z hz hs
  simpa [hs] using hz

theorem qCylinder_coordinates (z : ℍ) :
    AsymptoticCylinder.qCylinder (cylinder z)=Function.Periodic.qParam 1 (z:ℂ) := by
  rw [cylinder,AsymptoticCylinder.qCylinder_coe]
  congr 1
  exact Complex.re_add_im (z:ℂ)

/-- The lifted Fourier embedding is the literal capped holomorphic
section used by the reconstructed branch operators. -/
theorem lift_fourierMap (h t d : ℕ) {ε : ℝ} (hε : 0<ε)
    (hd : 2*d+4≤2*h+2*t+1) (a : AsymptoticCylinder.coefficientSpace d) :
    lift ((AsymptoticCylinder.fourierMap (2*h) t d (by positivity) hε hd a :
      AsymptoticCylinder.holomorphicSpace (2*h) t (by positivity : 0<4*Real.pi) hε):
      AsymptoticCylinder.Space) =ᵐ[volume]
      AsymptoticWeightedBranches.stripSection ε t (h+1) (FinitenessFourierConstruction.fourier a.val) := by
  apply (lift_coeFn_of_ae _ _ (AsymptoticCylinder.fourierMap_eq_disk_ae h t d hε hd a)).trans
  apply Filter.Eventually.of_forall
  intro z
  classical
  by_cases hz : z∈AsymptoticMassTransport.strip
  · rw [Set.indicator_of_mem hz,AsymptoticWeightedBranches.stripSection,Set.indicator_of_mem hz,
      AsymptoticWeightedBranches.weighted,qCylinder_coordinates]
    change (z.im:ℂ)*(((z.im^h*(min (z.im/ε) 1)^t:ℝ):ℂ)*
      FinitenessPolynomialSeries.sum a.val (Function.Periodic.qParam 1 (z:ℂ)))=_
    rw [FinitenessFourierConstruction.fourier,pow_succ]
    push_cast
    ring
  · simp [AsymptoticWeightedBranches.stripSection,hz]

#print axioms lift_coeFn
#print axioms lift_norm
#print axioms lift_fourierMap

end AsymptoticCylinderLift
