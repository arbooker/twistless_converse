module

public import QuantitativeMaassCuspGeneratorV1
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Const

set_option autoImplicit false
@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

/-- The literal differential operator depends only on the germ. -/
theorem hyperbolic_congr_eventually {u v : Point → ℂ} {Z : Point}
    (he : u=ᶠ[𝓝 Z] v) : hyperbolic u Z=hyperbolic v Z := by
  have hx : (fun x => u (x,Z.2))=ᶠ[𝓝 Z.1] (fun x => v (x,Z.2)) :=
    he.comp_tendsto ((continuous_id.prodMk continuous_const).continuousAt.tendsto)
  have hy : (fun y => u (Z.1,y))=ᶠ[𝓝 Z.2] (fun y => v (Z.1,y)) :=
    he.comp_tendsto ((continuous_const.prodMk continuous_id).continuousAt.tendsto)
  unfold hyperbolic euclidean
  rw [hx.deriv.deriv_eq,hy.deriv.deriv_eq]

theorem dir_finset_sum {ι : Type*} (S : Finset ι) (u : ι → Point → ℂ)
    {s : Set Point} (hs : IsOpen s) (hu : ∀ i∈S, ContDiffOn ℝ ∞ (u i) s)
    {Z : Point} (hZ : Z∈s) (v : Point) :
    dir v (fun W => ∑ i∈S, u i W) Z=∑ i∈S, dir v (u i) Z := by
  unfold dir D
  rw [fderiv_fun_sum (fun i hi => ((hu i hi).contDiffAt (hs.mem_nhds hZ)).differentiableAt (by simp))]
  simp

theorem dir2_finset_sum {ι : Type*} (S : Finset ι) (u : ι → Point → ℂ)
    {s : Set Point} (hs : IsOpen s) (hu : ∀ i∈S, ContDiffOn ℝ ∞ (u i) s)
    {Z : Point} (hZ : Z∈s) (v : Point) :
    dir v (dir v (fun W => ∑ i∈S, u i W)) Z=∑ i∈S, dir v (dir v (u i)) Z := by
  have he : EqOn (dir v (fun W => ∑ i∈S, u i W)) (fun W => ∑ i∈S, dir v (u i) W) s :=
    fun W hW => dir_finset_sum S u hs hu hW v
  rw [dir_congr hs he hZ v]
  exact dir_finset_sum S (fun i => dir v (u i)) hs
    (fun i hi => dir_contDiffOn (hu i hi) hs v) hZ v

/-- Finite local sums commute with the literal hyperbolic Laplacian. -/
theorem hyperbolic_finset_sum {ι : Type*} (S : Finset ι) (u : ι → Point → ℂ)
    (hu : ∀ i∈S, ContDiffOn ℝ ∞ (u i) {Z | 0<Z.2})
    (Z : Point) (hZ : 0<Z.2) :
    hyperbolic (fun W => ∑ i∈S, u i W) Z=∑ i∈S, hyperbolic (u i) Z := by
  have hs : IsOpen {Z : Point | 0<Z.2} := isOpen_lt continuous_const continuous_snd
  have hsum := ContDiffOn.sum (s := S) hu
  have he (f : Point → ℂ) (hf : ContDiffOn ℝ ∞ f {Z | 0<Z.2}) :
      hyperbolic f Z=-(Z.2^2) • (X (X f) Z+Y (Y f) Z) := by
    rw [XX_eq_deriv hf hs hZ,YY_eq_deriv hf hs hZ]
    rfl
  rw [he _ hsum]
  have hr : (∑ i∈S, hyperbolic (u i) Z)=
      ∑ i∈S, -(Z.2^2) • (X (X (u i)) Z+Y (Y (u i)) Z) :=
    Finset.sum_congr rfl (fun i hi => he _ (hu i hi))
  rw [hr]
  rw [show X (X (fun W => ∑ i∈S, u i W)) Z=∑ i∈S, X (X (u i)) Z from
    dir2_finset_sum S u hs hu hZ e₁,
    show Y (Y (fun W => ∑ i∈S, u i W)) Z=∑ i∈S, Y (Y (u i)) Z from
    dir2_finset_sum S u hs hu hZ e₂]
  simp only [Finset.sum_add_distrib,Finset.smul_sum,smul_add]

#print axioms hyperbolic_finset_sum
#print axioms hyperbolic_congr_eventually

end QuantitativeMaass
