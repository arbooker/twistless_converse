module

public import QuantitativeMaassMajorantRectangleMassV1
public import QuantitativeMaassCompactColumnEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory ContinuousLinearMap UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled

/-- The compact-input energy is the literal local diagonal energy for
the normalized majorant, before any bound on the upper cusp height. -/
theorem originalMajorant_compact_column_energy {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0)))
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (ε : ℝ→ℝ) (t : ℝ) (a b : ℝ) (ha : 0<a) :
    let S := upperRectangle 0 1 a b
    let P := AsymptoticRegionL2.projection (quotientMeasure 0) S
      (upperRectangle_compact 0 1 a b ha).measurableSet
    (∫ z,‖P (originalMajorantColumn K hc he ε t z)‖^2 ∂quotientMeasure 0)=
      ∫ z in S,‖originalMajorantColumn K hc he ε t z‖^2 := by
  exact compact_input_column_energy basis (QuantitativeNinaMaass.originalWindowMajorant K hc ε t)
    (QuantitativeNinaMaass.originalWindowMajorant_compact K hc ε t)
    (QuantitativeNinaMaass.originalWindowMajorant_even K he hc ε t)
    (QuantitativeNinaMaass.originalWindowMajorant_real K he hc ε t)
    (supportRadius K hc*radius ε t) (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le
    (originalMajorant_support K hc ε t) ha b

/-- Uniform compact-input mass costs only the inverse lower height.
In particular the source recovery term need not pay a strong-scale loss. -/
theorem originalMajorant_compact_column_energy_uniform {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0)))
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (H : ℝ) :
    ∃ B : ℝ,0<B ∧ ∀ ε : ℝ→ℝ,
      (∀ᶠ t in atTop,0<ε t ∧ ε t≤1) →
      Tendsto (fun t => ε t*slowScale t) atTop atTop →
      ∀ᶠ t in atTop,∀ a b : ℝ,∀ ha : 0<a,0≤b → b≤Real.exp (H*Strong.strongScale t) →
        let S := upperRectangle 0 1 a b
        let P := AsymptoticRegionL2.projection (quotientMeasure 0) S
          (upperRectangle_compact 0 1 a b ha).measurableSet
        (∫ z,‖P (originalMajorantColumn K hc he ε t z)‖^2 ∂quotientMeasure 0)≤a⁻¹*B*(t*ε t) := by
  obtain ⟨B,hB,hbound⟩ := originalMajorant_rectangle_mass_uniform K hc he hK hm H
  refine ⟨B,hB,?_⟩
  intro ε hε hp
  filter_upwards [hbound ε hε hp] with t ht
  intro a b ha hb hsize
  dsimp only
  rw [originalMajorant_compact_column_energy basis K hc he ε t a b ha]
  exact ht a b ha hb hsize

#print axioms originalMajorant_compact_column_energy
#print axioms originalMajorant_compact_column_energy_uniform
end QuantitativeMaass.Scheduled
