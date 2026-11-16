module

public import QuantitativeMaassEulerCoefficientV1
public import MaassKBesselEventualPosV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace QuantitativeMaass

/-- The actual Fourier--Bessel reconstruction determines every positive
coefficient. A sufficiently high line makes its Bessel factor nonzero. -/
theorem principalEulerWave_injective {b c : ℕ → ℂ}
    (hb : MaassOriginal.PolynomialGrowth b) (hc : MaassOriginal.PolynomialGrowth c)
    (hzero : b 0=c 0) (r : ℝ) (σ : ℕ)
    (he : ∀ x y : ℝ,0<y → principalEulerWave b r σ (x,y)=principalEulerWave c r σ (x,y)) :
    b=c := by
  funext n
  cases n with
  | zero => exact hzero
  | succ n =>
    let y := (r^2+1)/(2*Real.pi*((n+1:ℕ):ℝ))
    have hy : 0<y := by dsimp [y]; positivity
    have hfreq : 2*Real.pi*((n+1:ℕ):ℝ)*y=r^2+1 := by
      dsimp [y]
      field_simp
    have hK : (MaassKBessel.moment 0 r (2*Real.pi*((n+1:ℕ):ℝ)*y):ℂ)≠0 := by
      have hp : 0<MaassKBessel.moment 0 r (2*Real.pi*((n+1:ℕ):ℝ)*y) := by
        rw [hfreq,MaassKBessel.moment_zero]
        exact MaassKBessel.K_pos_of_large r (by positivity) (by nlinarith [sq_nonneg r])
      exact_mod_cast hp.ne'
    have hs : (Real.sqrt y:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr hy).ne'
    have hh : (∫ x in Ioc (0:ℝ) 1,eulerCharacter (-((n+1:ℕ):ℤ)) x*principalEulerWave b r σ (x,y))=
        (∫ x in Ioc (0:ℝ) 1,eulerCharacter (-((n+1:ℕ):ℤ)) x*principalEulerWave c r σ (x,y)) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x _
      dsimp only
      rw [he x y hy]
    rw [principalEulerWave_coefficient hb r σ n y hy,principalEulerWave_coefficient hc r σ n y hy] at hh
    exact mul_right_cancel₀ hK (mul_left_cancel₀ hs hh)

#print axioms principalEulerWave_injective

end QuantitativeMaass
