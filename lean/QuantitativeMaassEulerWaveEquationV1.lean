module

public import QuantitativeMaassEulerBesselEquationV1
public import QuantitativeMaassComplexSqrtV1
public import MaassFrickeCovarianceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem principalEulerWave_second_x {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ : ℕ) (x y : ℝ) (hy : 0<y) :
    deriv (deriv (fun u => principalEulerWave b r σ (u,y))) x =
      -(Real.sqrt y:ℂ)*((2*Real.pi:ℝ):ℂ)^2*principalWeightedSeries b r 0 2 σ (x,y) := by
  have hfirst : deriv (fun u => principalEulerWave b r σ (u,y))=
      fun u => ((Real.sqrt y:ℂ)*((2*Real.pi:ℝ):ℂ)*Complex.I)*principalWeightedSeries b r 0 1 (σ+1) (u,y) := by
    funext u
    have hh := (principalWeightedSeries_hasDerivAt_x hb r 0 0 σ u y hy).const_mul (Real.sqrt y:ℂ)
    rw [principalWeightedSeries_zero] at hh
    simpa only [principalEulerWave,mul_assoc] using hh.deriv
  rw [hfirst]
  rw [((principalWeightedSeries_hasDerivAt_x hb r 0 1 (σ+1) x y hy).const_mul
    ((Real.sqrt y:ℂ)*((2*Real.pi:ℝ):ℂ)*Complex.I)).deriv]
  simp only [Nat.add_assoc,one_add_one_eq_two,principalWeightedSeries_add_two]
  linear_combination ((Real.sqrt y:ℂ)*((2*Real.pi:ℝ):ℂ)^2*
    principalWeightedSeries b r 0 2 σ (x,y))*Complex.I_sq

theorem principalEulerWave_second_y {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ : ℕ) (x y : ℝ) (hy : 0<y) :
    deriv (deriv (fun u => principalEulerWave b r σ (x,u))) y =
      complexSqrtSecond (fun u => principalEulerCore b r σ (x,u))
        (fun u => -((2*Real.pi:ℝ):ℂ)*principalWeightedSeries b r 1 1 σ (x,u))
        (fun u => ((2*Real.pi:ℝ):ℂ)^2*principalWeightedSeries b r 2 2 σ (x,u)) y := by
  let f := fun u => principalEulerCore b r σ (x,u)
  let g := fun u => -((2*Real.pi:ℝ):ℂ)*principalWeightedSeries b r 1 1 σ (x,u)
  let h := fun u => ((2*Real.pi:ℝ):ℂ)^2*principalWeightedSeries b r 2 2 σ (x,u)
  have hf : ∀ u,0<u → HasDerivAt f (g u) u := fun u hu => principalEulerCore_first_y hb r σ x u hu
  have hg : HasDerivAt g (h y) y := by
    convert (principalWeightedSeries_hasDerivAt_y hb r 1 1 σ x y hy).const_mul (-((2*Real.pi:ℝ):ℂ)) using 1
    ring
  have he : deriv (fun u => principalEulerWave b r σ (x,u)) =ᶠ[𝓝 y] complexSqrtFirst f g := by
    filter_upwards [isOpen_Ioi.mem_nhds hy] with u hu
    exact (complexSqrtWave_hasDerivAt hu (hf u hu)).deriv
  rw [he.deriv_eq]
  exact (complexSqrtFirst_hasDerivAt hy (hf y hy) hg).deriv

/-- The actual original-coefficient reconstruction satisfies the hyperbolic
Laplace eigenfunction equation, with the original principal spectral parameter. -/
theorem principalEulerWave_hyperbolic {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ : ℕ) (x y : ℝ) (hy : 0<y) :
    MaassDifferential.hyperbolic (principalEulerWave b r σ) (x,y)=
      ((1/4+r^2:ℝ):ℂ)*principalEulerWave b r σ (x,y) := by
  have hsq : (Real.sqrt y:ℂ)^2=(y:ℂ) := by exact_mod_cast Real.sq_sqrt hy.le
  have hs : (Real.sqrt y:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr hy).ne'
  have hyc : (y:ℂ)≠0 := by exact_mod_cast hy.ne'
  have heq := principalWeightedSeries_bessel_equation hb r σ x y hy
  unfold MaassDifferential.hyperbolic MaassDifferential.euclidean
  rw [principalEulerWave_second_x hb r σ x y hy,principalEulerWave_second_y hb r σ x y hy]
  dsimp [complexSqrtSecond,principalEulerWave]
  push_cast at heq ⊢
  field_simp [hs,hyc]
  rw [hsq]
  linear_combination -(4*(y:ℂ))*heq

#print axioms principalEulerWave_second_x
#print axioms principalEulerWave_second_y
#print axioms principalEulerWave_hyperbolic

end QuantitativeMaass
