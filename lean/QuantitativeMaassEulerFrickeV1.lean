module

public import QuantitativeMaassEulerFrickeTransferV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Global even Fricke reflection from the literal original untwisted
functional equation and individual coefficient growth. -/
theorem principalEulerWave_even_fricke {b : ℕ → ℂ}
    (hb : MaassOriginal.PolynomialGrowth b) (L : ℝ) (hL : 0<L) (r : ℝ) (ε : ℂ)
    (hε : ‖ε‖=1) (hcont : MaassOriginal.Continuation L (.principal r) 0 b ε) :
    ∀ x y : ℝ,0<y → principalEulerWave b r 0 (x,y)=
      ε*principalEulerWave b r 0 (MaassDifferential.F L x y) := by
  apply principalEulerWave_fricke_from_axis hb L hL r 0 ε
  · exact principalEulerWave_even_physical_axis hb L hL r ε hε hcont
  · intro y hy
    rw [principalEulerWave_even_normal_zero hb r y hy,
      principalEulerWave_even_normal_zero hb r (1/(L*y)) (by positivity),mul_zero]

/-- Global odd Fricke reflection; the sign is minus the functional-equation
sign because Fricke reverses the normal direction on the axis. -/
theorem principalEulerWave_odd_fricke {b : ℕ → ℂ}
    (hb : MaassOriginal.PolynomialGrowth b) (L : ℝ) (hL : 0<L) (r : ℝ) (ε : ℂ)
    (hε : ‖ε‖=1) (hcont : MaassOriginal.Continuation L (.principal r) 1 b ε) :
    ∀ x y : ℝ,0<y → principalEulerWave b r 1 (x,y)=
      (-ε)*principalEulerWave b r 1 (MaassDifferential.F L x y) := by
  apply principalEulerWave_fricke_from_axis hb L hL r 1 (-ε)
  · intro y _
    rw [principalEulerWave_odd_axis_zero,principalEulerWave_odd_axis_zero,mul_zero]
  · intro y hy
    rw [principalEulerWave_odd_physical_normal hb L hL r ε hε hcont y hy]
    push_cast
    ring

/-- Parity-correct global Fricke reflection of the actual original Fourier
reconstruction. The only hypotheses are the original coefficient growth and
untwisted continuation/functional equation; no automorphy or PDE is assumed. -/
theorem principalEulerWave_fricke {b : ℕ → ℂ}
    (hb : MaassOriginal.PolynomialGrowth b) (L : ℝ) (hL : 0<L) (r : ℝ) (σ : ℕ)
    (hσ : σ=0 ∨ σ=1) (ε : ℂ) (hε : ‖ε‖=1)
    (hcont : MaassOriginal.Continuation L (.principal r) σ b ε) :
    ∀ x y : ℝ,0<y → principalEulerWave b r σ (x,y)=
      ((-1:ℂ)^σ*ε)*principalEulerWave b r σ (MaassDifferential.F L x y) := by
  rcases hσ with rfl|rfl
  · simpa only [pow_zero,one_mul] using principalEulerWave_even_fricke hb L hL r ε hε hcont
  · simpa only [pow_one,neg_one_mul] using principalEulerWave_odd_fricke hb L hL r ε hε hcont

#print axioms principalEulerWave_even_fricke
#print axioms principalEulerWave_odd_fricke
#print axioms principalEulerWave_fricke

end QuantitativeMaass
