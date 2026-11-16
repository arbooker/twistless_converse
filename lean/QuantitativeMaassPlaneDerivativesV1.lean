module

public import MaassSecondCurveV1
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass

def planeDerivative (v : ℝ × ℝ) (f : (ℝ × ℝ) → ℂ) (z : ℝ × ℝ) : ℂ :=
  fderiv ℝ f z v

theorem planeDerivative_contDiffOn {f : (ℝ × ℝ) → ℂ} {S : Set (ℝ × ℝ)}
    (hf : ContDiffOn ℝ ∞ f S) (hS : IsOpen S) (v : ℝ × ℝ) :
    ContDiffOn ℝ ∞ (planeDerivative v f) S := by
  exact (hf.fderiv_of_isOpen hS (by simp)).clm_apply contDiffOn_const

theorem planeDerivative_second {f : (ℝ × ℝ) → ℂ} {S : Set (ℝ × ℝ)}
    (hf : ContDiffOn ℝ ∞ f S) (hS : IsOpen S) (v w z : ℝ × ℝ) (hz : z∈S) :
    planeDerivative w (planeDerivative v f) z=fderiv ℝ (fderiv ℝ f) z w v := by
  have hD : DifferentiableAt ℝ (fderiv ℝ f) z :=
    ((hf.fderiv_of_isOpen hS (m:=1) (by simp)).contDiffAt (hS.mem_nhds hz)).differentiableAt (by norm_num)
  unfold planeDerivative
  rw [fderiv_clm_apply hD (differentiableAt_const _)]
  simp

/-- Mixed directional derivatives commute for the actual smooth functions on
an open set, by Schwarz symmetry of the second Frechet derivative. -/
theorem planeDerivative_commute {f : (ℝ × ℝ) → ℂ} {S : Set (ℝ × ℝ)}
    (hf : ContDiffOn ℝ ∞ f S) (hS : IsOpen S) (v w z : ℝ × ℝ) (hz : z∈S) :
    planeDerivative w (planeDerivative v f) z=planeDerivative v (planeDerivative w f) z := by
  rw [planeDerivative_second hf hS v w z hz,planeDerivative_second hf hS w v z hz]
  exact ((hf.contDiffAt (hS.mem_nhds hz)).isSymmSndFDerivAt (by simp)).eq w v

theorem planeDerivative_congr_on {f g : (ℝ × ℝ) → ℂ} {S : Set (ℝ × ℝ)}
    (hS : IsOpen S) (hfg : EqOn f g S) (v z : ℝ × ℝ) (hz : z∈S) :
    planeDerivative v f z=planeDerivative v g z := by
  have he : f =ᶠ[𝓝 z] g := Filter.Eventually.mono (hS.mem_nhds hz) (fun w hw => hfg hw)
  exact congrArg (fun A : (ℝ × ℝ) →L[ℝ] ℂ => A v) he.fderiv_eq

theorem planeDerivative_horizontal {f : (ℝ × ℝ) → ℂ} {S : Set (ℝ × ℝ)}
    (hf : ContDiffOn ℝ ∞ f S) (hS : IsOpen S) (x y : ℝ) (hz : (x,y)∈S) :
    deriv (fun u => f (u,y)) x=planeDerivative (1,0) f (x,y) := by
  have hd := ((hf.contDiffAt (hS.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt
  exact (hd.comp_hasDerivAt (l:=f) x ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))).deriv

theorem planeDerivative_vertical {f : (ℝ × ℝ) → ℂ} {S : Set (ℝ × ℝ)}
    (hf : ContDiffOn ℝ ∞ f S) (hS : IsOpen S) (x y : ℝ) (hz : (x,y)∈S) :
    deriv (fun u => f (x,u)) y=planeDerivative (0,1) f (x,y) := by
  have hd := ((hf.contDiffAt (hS.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt
  exact (hd.comp_hasDerivAt (l:=f) y ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))).deriv

#print axioms planeDerivative_contDiffOn
#print axioms planeDerivative_second
#print axioms planeDerivative_commute
#print axioms planeDerivative_congr_on
#print axioms planeDerivative_horizontal
#print axioms planeDerivative_vertical

end QuantitativeMaass
