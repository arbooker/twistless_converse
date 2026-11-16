module

public import MaassFrickeAccelerationV1
public import MaassBilinearRotationV1
public import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option maxHeartbeats 30000

@[expose] public section

open Set Filter
open scoped Topology ContDiff

namespace MaassDifferential

noncomputable def euclidean (u : Point → ℂ) (Z : Point) : ℂ :=
  deriv (deriv (fun x => u (x,Z.2))) Z.1 +
    deriv (deriv (fun y => u (Z.1,y))) Z.2

noncomputable def hyperbolic (u : Point → ℂ) (Z : Point) : ℂ :=
  -(Z.2^2) • euclidean u Z

noncomputable def pullback (L : ℝ) (u : Point → ℂ) (Z : Point) : ℂ :=
  u (F L Z.1 Z.2)

theorem euclidean_pullback {u : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    {L x y : ℝ} (hL : 0<L) (hy : 0<y) :
    euclidean (pullback L u) (x,y) =
      (a L x y^2+b L x y^2) • euclidean u (F L x y) := by
  have hs : IsOpen {Z : Point | 0<Z.2} := isOpen_lt continuous_const continuous_snd
  have hr : x^2+y^2≠0 := (radius_pos hy).ne'
  have hm : F L x y∈{Z : Point | 0<Z.2} := F_height_pos hL hy
  have hx := second_curve hu hs (g := fun z => F L z y)
    (g' := fun z => (a L z y,-b L z y))
    (Eventually.of_forall (fun z => F_hasDerivAt_X hL (radius_pos hy).ne'))
    (velocity_hasDerivAt_X hL hr) hm
  have hg : ∀ᶠ z in 𝓝 y, HasDerivAt (fun z => F L x z) (b L x z,a L x z) z := by
    filter_upwards [isOpen_Ioi.mem_nhds hy] with z hz
    exact F_hasDerivAt_Y hL (radius_pos hz).ne'
  have hyy := second_curve hu hs (g := fun z => F L x z)
    (g' := fun z => (b L x z,a L x z)) hg (velocity_hasDerivAt_Y hL hr) hm
  change deriv (deriv (fun z => u (F L z y))) x +
    deriv (deriv (fun z => u (F L x z))) y = _
  rw [hx,hyy]
  have hn : (-aa L x y,-bb L x y)=-(aa L x y,bb L x y) := rfl
  rw [hn,map_neg]
  have hh : H u (F L x y) (a L x y,-b L x y) (a L x y,-b L x y) +
      D u (F L x y) (aa L x y,bb L x y) +
      (H u (F L x y) (b L x y,a L x y) (b L x y,a L x y) -
      D u (F L x y) (aa L x y,bb L x y)) =
      H u (F L x y) (a L x y,-b L x y) (a L x y,-b L x y) +
      H u (F L x y) (b L x y,a L x y) (b L x y,a L x y) := by abel
  rw [← sub_eq_add_neg,hh,bilinear_rotation]
  congr 1
  unfold euclidean
  exact (congrArg₂ (· + ·)
    (second_horizontal hu hs (x := (F L x y).1) (y := (F L x y).2) hm)
    (second_vertical hu hs (x := (F L x y).1) (y := (F L x y).2) hm)).symm

/-- Hyperbolic Laplace covariance under the exact real Fricke map. -/
theorem hyperbolic_pullback {u : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    {L x y : ℝ} (hL : 0<L) (hy : 0<y) :
    hyperbolic (pullback L u) (x,y) = hyperbolic u (F L x y) := by
  unfold hyperbolic
  rw [euclidean_pullback hu hL hy,smul_smul]
  change (-(y^2)*(a L x y^2+b L x y^2)) • euclidean u (F L x y) = _
  rw [neg_mul,F_scale hL (radius_pos hy).ne']

#print axioms euclidean_pullback
#print axioms hyperbolic_pullback

end MaassDifferential
