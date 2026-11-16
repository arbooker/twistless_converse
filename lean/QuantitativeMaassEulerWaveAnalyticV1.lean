module

public import QuantitativeMaassEulerAnalyticCurvesV1
public import Mathlib.Analysis.Complex.SqrtDeriv

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

def complexEulerWave (b : ℕ → ℂ) (r : ℝ) (σ : ℕ) (x y : ℂ) : ℂ :=
  Complex.sqrt y*complexEulerCore b r σ x y

theorem complexEulerWave_ofReal (b : ℕ → ℂ) (r : ℝ) (σ : ℕ) (x y : ℝ) (hy : 0≤y) :
    complexEulerWave b r σ (x:ℂ) (y:ℂ)=principalEulerWave b r σ (x,y) := by
  unfold complexEulerWave principalEulerWave
  rw [complexEulerCore_ofReal,Complex.sqrt_of_nonneg (by exact_mod_cast hy)]
  rfl

/-- Holomorphic regularity of the full wave, including its sqrt(height) factor,
along every holomorphic coordinate curve inside the physical tube. -/
theorem complexEulerWave_analytic_curves {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ : ℕ) (X Y : ℂ → ℂ) (S : Set ℂ) (hS : IsOpen S)
    (hX : DifferentiableOn ℂ X S) (hY : DifferentiableOn ℂ Y S)
    (hgap : ∀ z∈S,|(X z).im|<(Y z).re) :
    AnalyticOnNhd ℂ (fun z => complexEulerWave b r σ (X z) (Y z)) S := by
  have hs := Complex.differentiableOn_sqrt.comp hY (fun z hz =>
    Or.inl ((abs_nonneg _).trans_lt (hgap z hz)))
  exact (hs.mul (complexEulerCore_analytic_curves hb r σ X Y S hS hX hY hgap).differentiableOn).analyticOnNhd hS

/-- The actual physical wave is real analytic in its horizontal variable at
every point of the upper half-plane. -/
theorem principalEulerWave_analytic_horizontal {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ : ℕ) (y : ℝ) (hy : 0<y) :
    AnalyticOnNhd ℝ (fun x => principalEulerWave b r σ (x,y)) univ := by
  let S := {z : ℂ | |z.im|<y}
  have hS : IsOpen S := isOpen_lt Complex.continuous_im.abs continuous_const
  have ha := complexEulerWave_analytic_curves hb r σ id (fun _ => (y:ℂ)) S hS
    differentiableOn_id (differentiableOn_const _) (fun z hz => hz)
  intro x _
  have hx : (x:ℂ)∈S := by simpa [S] using hy
  have hh : AnalyticAt ℝ (fun u : ℝ => complexEulerWave b r σ (u:ℂ) (y:ℂ)) x :=
    ((ha (x:ℂ) hx).restrictScalars (𝕜:=ℝ)).comp (Complex.ofRealCLM.analyticAt x)
  simpa only [complexEulerWave_ofReal b r σ _ y hy.le] using hh

#print axioms complexEulerWave_ofReal
#print axioms complexEulerWave_analytic_curves
#print axioms principalEulerWave_analytic_horizontal

end QuantitativeMaass
