module

public import QuantitativeMaassEulerCompleteAverageV1
public import QuantitativeMaassEulerComplexPhysicalV1
public import QuantitativeMaassEulerSectorsV1
public import AsymptoticCylinderRamifiedV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass
open AsymptoticSectorSigns

/-- Reinserting sqrt(y) changes the complete-average coefficient from p
on the Fourier core to sqrt(p) on the physical Maass wave. -/
theorem principalEulerWave_average_of_row {b : ℕ→ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ : ℕ) {p : ℕ} (hp : 0<p) (c : ℂ)
    (hrow : ∀ n,b (p*n)=c*b n) (x y : ℝ) (hy : 0<y) :
    (∑ a∈Finset.range p,principalEulerWave b r σ ((x+(a:ℝ))/p,y/p))=
      (Real.sqrt p:ℂ)*c*principalEulerWave b r σ (x,y) := by
  have hpR : (0:ℝ)<p := by exact_mod_cast hp
  have hs : Real.sqrt (y/p)*Real.sqrt p=Real.sqrt y := by
    rw [←Real.sqrt_mul (div_nonneg hy.le hpR.le),div_mul_cancel₀ y hpR.ne']
  have hscale : Real.sqrt (y/p)*(p:ℝ)=Real.sqrt p*Real.sqrt y := by
    have hsq := Real.sq_sqrt hpR.le
    calc
      _ = (Real.sqrt (y/p)*Real.sqrt p)*Real.sqrt p := by linear_combination -(Real.sqrt (y/p))*hsq
      _ = _ := by rw [hs];ring
  have hscaleC : (Real.sqrt (y/p):ℂ)*(p:ℂ)=(Real.sqrt p:ℂ)*(Real.sqrt y:ℂ) := by
    exact_mod_cast hscale
  simp only [principalEulerWave]
  rw [←Finset.mul_sum,principalEulerCore_average_of_row hb r σ hp c hrow x y hy]
  calc
    _ = ((Real.sqrt (y/p):ℂ)*(p:ℂ))*c*principalEulerCore b r σ (x,y) := by ring
    _ = _ := by rw [hscaleC];ring

theorem principalEulerPhysical_average_of_row {b : ℕ→ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ : ℕ) {p : ℕ} (hp : 0<p) (c : ℂ)
    (hrow : ∀ n,b (p*n)=c*b n) (z : ℂ) (hz : 0<z.im) :
    (∑ a∈Finset.range p,principalEulerPhysical b r σ ((z+(a:ℂ))/p))=
      (Real.sqrt p:ℂ)*c*principalEulerPhysical b r σ z := by
  simpa only [principalEulerPhysical,←Complex.ofReal_natCast,Complex.div_ofReal_re,
    Complex.div_ofReal_im,Complex.add_re,Complex.add_im,Complex.ofReal_re,
    Complex.ofReal_im,add_zero] using
      principalEulerWave_average_of_row hb r σ hp c hrow z.re z.im hz

/-- Original Euler data supplies every ramified equation with its actual
finite sector sign. There is no assumed Maass eigenrelation. -/
theorem principalEulerPhysical_ramified {N : ℕ} {b : ℕ→ℂ}
    (r : ℝ) (σ : ℕ) (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b)
    (e : Sector N) (he : ∀ p,p∈simplePrimes N → delta e p=b p*(Real.sqrt p:ℂ))
    {p : ℕ} (hp : p.Prime) (hpN : p∣N) (z : ℂ) (hz : 0<z.im) :
    (∑ a∈Finset.range p,principalEulerPhysical b r σ ((z+(a:ℂ))/p))=
      AsymptoticCylinderRamified.eigenvalue e p*principalEulerPhysical b r σ z := by
  have hcoef : (Real.sqrt p:ℂ)*b p=AsymptoticCylinderRamified.eigenvalue e p := by
    by_cases hs : p^2∣N
    · rw [AsymptoticCylinderRamified.eigenvalue,ite_eq_left hs,
        FinitenessOriginalTwistLocal.bad_parameter_zero hb.toEulerData hp hs,mul_zero]
    · rw [AsymptoticCylinderRamified.eigenvalue,ite_eq_right hs,
        he p (mem_simplePrimes.mpr ⟨hp,hpN,hs⟩),mul_comm]
  rw [principalEulerPhysical_average_of_row hb.polynomialGrowth r σ hp.pos (b p)
    (AsymptoticRamifiedCoefficients.bad_mul hb.toEulerData hp hpN) z hz,hcoef]

#print axioms principalEulerWave_average_of_row
#print axioms principalEulerPhysical_average_of_row
#print axioms principalEulerPhysical_ramified
end QuantitativeMaass
