module

public import QuantitativeMaassMajorantColumnsV1

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled

/-- The support radius can be enlarged to accommodate the finite inverse
cap while keeping the literal packet unchanged. -/
theorem originalMajorant_support_enlarged (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (ε : ℝ→ℝ) (t C : ℝ) (hC : supportRadius K hc≤C) :
    Function.support (QuantitativeNinaMaass.originalWindowMajorant K hc ε t)⊆
      Icc (-(C*radius ε t)) (C*radius ε t) := by
  intro x hx
  have hh := originalMajorant_support K hc ε t hx
  have hr := mul_le_mul_of_nonneg_right hC (radius_pos ε t).le
  exact ⟨(neg_le_neg hr).trans hh.1,hh.2.trans hr⟩

/-- The radius occurs only in the proof of square integrability of these
columns; enlarging it gives the same Hilbert-space vector. -/
theorem originalMajorantColumn_eq_enlarged_radius (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (he : Function.Even K)
    (ε : ℝ→ℝ) (t C : ℝ) (hC : supportRadius K hc≤C) (z : ℍ) :
    originalMajorantColumn K hc he ε t z=
      cylinderTimeColumn (QuantitativeNinaMaass.originalWindowMajorant K hc ε t)
        (QuantitativeNinaMaass.originalWindowMajorant_compact K hc ε t)
        (QuantitativeNinaMaass.originalWindowMajorant_even K he hc ε t)
        (C*radius ε t) (mul_nonneg ((supportRadius_pos K hc).le.trans hC) (radius_pos ε t).le)
        (originalMajorant_support_enlarged K hc ε t C hC) z := by
  rfl

#print axioms originalMajorant_support_enlarged
#print axioms originalMajorantColumn_eq_enlarged_radius
end QuantitativeMaass.Scheduled
