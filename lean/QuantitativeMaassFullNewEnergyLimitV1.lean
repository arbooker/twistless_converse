module

public import QuantitativeMaassFullNewParityEnergySumV1
public import QuantitativeNinaMaassNewParityEnergyAsymptoticV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory AsymptoticClassicalPetersson QuantitativeNinaMaass
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass

/-- The literal full newspace majorant packet has twice the parity
coefficient, with no exceptional-spectrum or parity-completeness premise. -/
theorem originalNewWindowPacket_energy_limit {ι κ ρ : Type*}
    (N : ℕ) [NeZero N] (hN : GridAdmissibleGap.Admissible N)
    (b : HilbertBasis ι ℂ (completedCuspidalNewSpace N hN.1))
    (bp : HilbertBasis κ ℂ (completedCuspidalNewParitySpace N hN.1 1))
    (bm : HilbertBasis ρ ℂ (completedCuspidalNewParitySpace N hN.1 (-1)))
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => hilbertSchmidtEnergy b
      (completedCuspidalNewTimePacket N hN.1 (originalWindowMajorant K hc ε t)
        ((originalWindowMajorant K hc ε t).smooth ⊤) (originalWindowMajorant_compact K hc ε t))/(t*ε t))
      atTop (𝓝 (2*AsymptoticTotalNewCorner.arithmeticCoefficient N)) := by
  have hp1 := originalNewParityWindowPacket_energy_limit N hN 1 (by norm_num) bp K he hc hK hm ε hε hp
  have hm1 := originalNewParityWindowPacket_energy_limit N hN (-1) (by norm_num) bm K he hc hK hm ε hε hp
  convert hp1.add hm1 using 1
  · funext t
    rw [completedCuspidalNewTimePacket_parity_energy_sum N hN.1 1 (by norm_num) b bp bm
      (originalWindowMajorant K hc ε t) (originalWindowMajorant_compact K hc ε t)
      (originalWindowMajorant_even K he hc ε t) (originalWindowMajorant_real K he hc ε t)
      (originalWindowPropagationConstant K hc*positiveWindowRadius ε t)
      (mul_pos (originalWindowPropagationConstant_pos K hc) (positiveWindowRadius_pos ε t)).le
      (originalWindowPropagationConstant_support K hc ε t),add_div]
    rfl
  · congr 1
    ring

#print axioms originalNewWindowPacket_energy_limit
end QuantitativeMaass
