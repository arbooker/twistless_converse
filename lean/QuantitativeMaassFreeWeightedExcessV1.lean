module

public import QuantitativeMaassFreeRegularFamilyV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open UpperHalfPlane MeasureTheory ContinuousLinearMap AsymptoticRegularTrace
open scoped lp ENNReal
namespace QuantitativeMaass.FreeRegularFamily

/-- The semifinite weighted estimate needs fixing only on free rational
orbits. The removed invariant null set changes none of the traces. -/
theorem weighted_excess (B F E : ℍ→Space→L[ℂ]Space)
    (hmB : ∀ a b,Measurable (fun x => matrix (B x) a b))
    (hmF : ∀ a b,Measurable (fun x => matrix (F x) a b))
    (hmE : ∀ a b,Measurable (fun x => matrix (E x) a b))
    (hcB : Covariant B) (hcF : Covariant F) (hcE : Covariant E)
    (hp : ∀ x,0≤F x ∧ F x≤1) (hE : ∀ x,IsStarProjection (E x))
    (hf : trace volume F<∞) (he : trace volume E<∞)
    {C δ : ℝ} (hC : 0≤C) (hδ : 0≤δ) (hb : ∀ x,‖B x‖≤C)
    (hfix : ∀ x,free x → ‖F x*E x-E x‖≤δ) :
    |signedTrace volume (fun x => B x*(F x-E x))|≤
      C*(signedTrace volume F-(trace volume E).toReal+4*δ*(trace volume E).toReal) := by
  have hFr := family_regular F hmF hcF
  have hEr := family_regular E hmE hcE
  have hFf : trace volume (family F)<∞ := by rw [family_trace];exact hf
  have hEf : trace volume (family E)<∞ := by rw [family_trace];exact he
  have hpo := family_order F hp
  have heq : signedTrace volume (fun x => B x*(family F x-family E x))=
      signedTrace volume (fun x => B x*(F x-E x)) := by
    unfold signedTrace
    apply integral_congr_ae
    filter_upwards [family_ae F,family_ae E] with x hx hy
    rw [hx,hy]
  let : TopologicalSpace ℍ := ⊥
  let : DiscreteTopology ℍ := ⟨rfl⟩
  have hh := signedTrace_weighted_projection_excess volume AsymptoticRationalGroup.measurePreserving
    B (family F) (family E) hmB hFr.1 hEr.1 hcB hFr.2 hEr.2
    (fun x => (hpo x).1) (fun x => (hpo x).2) (family_projection E hE) hFf hEf hC hδ hb
    (family_fix F E hδ hfix)
  rw [heq,family_signedTrace,family_trace] at hh
  exact hh

#print axioms weighted_excess
end QuantitativeMaass.FreeRegularFamily
