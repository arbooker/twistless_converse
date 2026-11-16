module

public import QuantitativeMaassCylinderSharpCuspV1
public import QuantitativeMaassCylinderCenteredCappedV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped SchwartzMap ENNReal

namespace QuantitativeMaass

variable (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
  (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
  (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)

/-- The sharp inverse-height estimate for the actual nonzero-mode
terminal operator, including its full Hilbert-Schmidt sum. -/
theorem cylinderCenteredTerminalPacket_sharp_energy {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0))) (H : ℝ) (hH : 0<H) :
    (∑' i,ENNReal.ofReal (‖cylinderCenteredTerminalPacket f hc he hr R hR hs H hH (basis i)‖^2))≤
      ENNReal.ofReal H⁻¹*ENNReal.ofReal
        (abelProfile (evenCoshLift (timeConvolution f f)) 1).re := by
  rw [cylinderCenteredTerminalPacket,finiteEnergyColumnOperator_energy]
  exact cylinderTimeColumn_centered_sharp_tail f hc he hr R hR hs H hH

/-- Finite-band conjugation preserves the sharp cusp decay with its
explicit band factor; no global bounded inverse weight is assumed. -/
theorem cylinderCenteredCappedTerminalPacket_sharp_energy {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0))) (ε : ℝ) (m : ℕ)
    (H : ℝ) (hH : 0<H) :
    let J := ⌈(m:ℝ)*R+1⌉₊
    (∑' i,ENNReal.ofReal
      (‖cylinderCenteredCappedTerminalPacket f hc he hr R hR hs ε m H hH (basis i)‖^2))≤
      ENNReal.ofReal ((((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1))^2)*
        (ENNReal.ofReal H⁻¹*ENNReal.ofReal
          (abelProfile (evenCoshLift (timeConvolution f f)) 1).re) := by
  dsimp only
  let J := ⌈(m:ℝ)*R+1⌉₊
  let C : ℝ := ((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1)
  rw [cylinderCenteredCappedTerminalPacket_energy]
  have hb (z : ℍ) : ‖cylinderCenteredCappedColumn f hc he R hR hs ε m z‖≤
      C*‖cylinderCenteredTimeColumn f hc he R hR hs z‖ :=
    LogBands.conjugatedColumn_norm_bound _ _ _ _ J z
  have hsq (z : ℍ) : ‖cylinderCenteredCappedColumn f hc he R hR hs ε m z‖^2≤
      C^2*‖cylinderCenteredTimeColumn f hc he R hR hs z‖^2 := by
    calc
      _≤(C*‖cylinderCenteredTimeColumn f hc he R hR hs z‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hb z) 2
      _=_ := mul_pow _ _ _
  calc
    _≤∫⁻ z in AsymptoticCertificateOperators.highStrip H,
        ENNReal.ofReal (C^2)*ENNReal.ofReal (‖cylinderCenteredTimeColumn f hc he R hR hs z‖^2) := by
      apply lintegral_mono
      intro z
      dsimp only
      rw [←ENNReal.ofReal_mul (sq_nonneg C)]
      exact ENNReal.ofReal_le_ofReal (hsq z)
    _=ENNReal.ofReal (C^2)*(∫⁻ z in AsymptoticCertificateOperators.highStrip H,
        ENNReal.ofReal (‖cylinderCenteredTimeColumn f hc he R hR hs z‖^2)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _≤_ := mul_le_mul' le_rfl (cylinderTimeColumn_centered_sharp_tail f hc he hr R hR hs H hH)

#print axioms cylinderCenteredTerminalPacket_sharp_energy
#print axioms cylinderCenteredCappedTerminalPacket_sharp_energy

end QuantitativeMaass
