module

public import QuantitativeMaassBroadDeficitControlV1

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory

namespace QuantitativeMaass

/-- The full noncuspidal column energy is controlled by an unfiltered
broad deficit trace and the actual broad approximation error. -/
theorem filtered_packet_noncuspidal_integral_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (N p : ℕ) [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1) (d : ℕ)
    (Q F : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (x : α → AutomorphicSpace N) (hx : MemLp x 2 μ) :
    (∫ z, ‖F (x z)-F (localCuspidalProjection N hN (x z))‖^2 ∂μ) ≤
      ‖F‖^2*(2*(∫ z, ‖actualLVDeficit N p hN hpN a b hab d (Q (x z))‖^2 ∂μ)+
        2*(∫ z, ‖Q (x z)-x z‖^2 ∂μ)) := by
  let D := actualLVDeficit N p hN hpN a b hab d
  have hfx := (hx.continuousLinearMap_comp F).sub
    ((hx.continuousLinearMap_comp (localCuspidalProjection N hN)).continuousLinearMap_comp F)
  have hdq := (hx.continuousLinearMap_comp Q).continuousLinearMap_comp D
  have hqx := (hx.continuousLinearMap_comp Q).sub hx
  have hfi := (memLp_two_iff_integrable_sq_norm hfx.aestronglyMeasurable).mp hfx
  have hdi := (memLp_two_iff_integrable_sq_norm hdq.aestronglyMeasurable).mp hdq
  have hqi := (memLp_two_iff_integrable_sq_norm hqx.aestronglyMeasurable).mp hqx
  calc
    _ ≤ ∫ z, ‖F‖^2*(2*‖D (Q (x z))‖^2+2*‖Q (x z)-x z‖^2) ∂μ := by
      apply integral_mono hfi (((hdi.const_mul 2).add (hqi.const_mul 2)).const_mul (‖F‖^2))
      intro z
      exact filtered_packet_noncuspidal_error_sq N p hN hpN hNp hpres a b hab d Q F (x z)
    _ = _ := by
      have hh := integral_add (hdi.const_mul 2) (hqi.const_mul 2)
      simp only [Pi.sub_apply] at hh
      rw [integral_const_mul,hh]
      simp only [integral_const_mul]
      rfl

#print axioms filtered_packet_noncuspidal_integral_le

end QuantitativeMaass
