module

public import QuantitativeMaassCompactColumnCyclicityV1
public import QuantitativeMaassConcreteExpressionTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticClassicalPetersson AsymptoticMassTransport AsymptoticFiniteBranch
open scoped SchwartzMap
namespace QuantitativeMaass

/-- Physical and cylinder region restrictions intertwine with the actual
zero extension, including the translation-strip indicator. -/
theorem cylinderZeroExtension_projection (S : Set ℍ) (hS : MeasurableSet S) :
    (AsymptoticRegionL2.projection volume S hS).comp cylinderZeroExtension.toContinuousLinearMap=
      cylinderZeroExtension.toContinuousLinearMap.comp (AsymptoticRegionL2.projection (quotientMeasure 0) S hS) := by
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  have hz := cylinderZeroExtension_coeFn_of_ae _ _
    (AsymptoticRegionL2.projection_coeFn (quotientMeasure 0) S hS v)
  filter_upwards [AsymptoticRegionL2.projection_coeFn volume S hS (cylinderZeroExtension v),
    cylinderZeroExtension_coeFn v,hz] with z hp hv hz
  change AsymptoticRegionL2.projection volume S hS (cylinderZeroExtension v) z=
    cylinderZeroExtension (AsymptoticRegionL2.projection (quotientMeasure 0) S hS v) z
  rw [hp,hz]
  classical
  by_cases hzS : z∈S <;> by_cases hzstrip : z∈strip <;> simp [hzS,hzstrip] at hv ⊢ <;> exact hv

variable (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
  (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
  (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)

include hr in
/-- The compact column packet extended by zero is the physical compact
restriction of the actual cylinder wave. Boundary measure equality is used
explicitly for the closed rectangle. -/
theorem compact_column_physical_projection {a : ℝ} (ha : 0<a) (b : ℝ)
    (v : Lp ℂ 2 (quotientMeasure 0)) :
    let S := upperRectangle 0 1 a b
    let hS := upperRectangle_compact 0 1 a b ha
    AsymptoticZeroExtension.isometry volume S hS.measurableSet
      (cylinderCompactColumnPacket f hc he R hR hs S hS v)=
      AsymptoticRegionL2.projection volume S hS.measurableSet
        (cylinderZeroExtension (cylinderTimePacket f (f.smooth ⊤) hc v)) := by
  intro S hS
  let C := cylinderCompactColumnPacket f hc he R hR hs S hS
  have hcol := finiteEnergyColumnOperator_coeFn (volume.restrict S)
    (cylinderTimeColumn f hc he R hR hs)
    (compact_column_memLp _ (cylinderAbelColumn_continuous _ _ R hR _) S hS) v
  have hw := cylinderZeroExtension_coeFn_of_ae _ _
    (cylinderTimePacket_column_coeFn f (f.smooth ⊤) he hc hr R hR hs
      (evenCoshLift_support_of_time_support f R hR hs) v)
  have hle : volume.restrict S≤quotientMeasure 0 := by
    rw [←cylinder_rectangle_measure a b ha]
    exact Measure.restrict_le_self
  have hstrip : ∀ᵐ z ∂volume.restrict S,z∈strip := by
    apply (ae_mono hle)
    rw [translation_quotient_measure]
    exact ae_restrict_mem strip_measurable
  have hlocal : (C v : ℍ→ℂ)=ᵐ[volume.restrict S]
      (cylinderZeroExtension (cylinderTimePacket f (f.smooth ⊤) hc v) : ℍ→ℂ) := by
    filter_upwards [hcol,hw.filter_mono (ae_mono Measure.restrict_le_self),hstrip] with z hcol hw hz
    dsimp only [C,cylinderCompactColumnPacket]
    rw [hcol,hw,indicator_of_mem hz]
    simp only [cylinderTimeColumn]
  apply Lp.ext
  exact (AsymptoticZeroExtension.isometry_coeFn volume S hS.measurableSet (C v)).trans
    (((ae_eq_restrict_iff_indicator_ae_eq hS.measurableSet).mp hlocal).trans
      (AsymptoticRegionL2.projection_coeFn volume S hS.measurableSet
        (cylinderZeroExtension (cylinderTimePacket f (f.smooth ⊤) hc v))).symm)

include hr in
theorem compact_column_zeroExtension {a : ℝ} (ha : 0<a) (b : ℝ)
    (v : Lp ℂ 2 (quotientMeasure 0)) :
    let S := upperRectangle 0 1 a b
    let hS := upperRectangle_compact 0 1 a b ha
    AsymptoticZeroExtension.isometry volume S hS.measurableSet
      (cylinderCompactColumnPacket f hc he R hR hs S hS v)=
      cylinderZeroExtension (AsymptoticRegionL2.projection (quotientMeasure 0) S hS.measurableSet
        (cylinderTimePacket f (f.smooth ⊤) hc v)) := by
  intro S hS
  rw [compact_column_physical_projection f hc he hr R hR hs ha b v]
  exact DFunLike.congr_fun (cylinderZeroExtension_projection S hS.measurableSet) _

#print axioms cylinderZeroExtension_projection
#print axioms compact_column_physical_projection
#print axioms compact_column_zeroExtension
end QuantitativeMaass
