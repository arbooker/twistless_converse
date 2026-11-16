module

public import MaassSecondCurveV1
public import Mathlib.Analysis.Calculus.Deriv.Prod

set_option autoImplicit false
set_option maxHeartbeats 20000

@[expose] public section

open Set Filter
open scoped Topology ContDiff

namespace MaassDifferential

noncomputable def dir (v : Point) (u : Point → ℂ) (Z : Point) : ℂ := D u Z v
noncomputable def X := dir e₁
noncomputable def Y := dir e₂

theorem dir_contDiffOn {u : Point → ℂ} {s : Set Point}
    (hu : ContDiffOn ℝ ∞ u s) (hs : IsOpen s) (v : Point) :
    ContDiffOn ℝ ∞ (dir v u) s := by
  have hD : ContDiffOn ℝ ∞ (D u) s := hu.fderiv_of_isOpen hs (by simp)
  exact hD.clm_apply contDiffOn_const

theorem dir_congr {u v : Point → ℂ} {s : Set Point} (hs : IsOpen s)
    (he : EqOn u v s) {z : Point} (hz : z∈s) (w : Point) : dir w u z=dir w v z := by
  have h : u=ᶠ[𝓝 z] v := eventually_of_mem (hs.mem_nhds hz) he
  exact congrArg (fun A : Point →L[ℝ] ℂ => A w) h.fderiv_eq

theorem dir_dir {u : Point → ℂ} {s : Set Point}
    (hu : ContDiffOn ℝ ∞ u s) (hs : IsOpen s) {z : Point} (hz : z∈s)
    (v w : Point) : dir w (dir v u) z = H u z w v := by
  have huD : ContDiffOn ℝ 1 (D u) s := hu.fderiv_of_isOpen hs (by simp)
  have hd := ((huD.contDiffAt (hs.mem_nhds hz)).differentiableAt (by norm_num)).hasFDerivAt
  have h := hd.clm_apply (hasFDerivAt_const v z)
  have he := congrArg (fun A : Point →L[ℝ] ℂ => A w) h.fderiv
  unfold dir D H
  simpa [D] using he

theorem horizontal_hasDerivAt {u : Point → ℂ} {s : Set Point}
    (hu : ContDiffOn ℝ ∞ u s) (hs : IsOpen s) {x y : ℝ} (hz : (x,y)∈s) :
    HasDerivAt (fun z => u (z,y)) (X u (x,y)) x := by
  have hd := ((hu.contDiffAt (hs.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt
  exact hd.comp_hasDerivAt x ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))

theorem X_eq_deriv {u : Point → ℂ} {s : Set Point}
    (hu : ContDiffOn ℝ ∞ u s) (hs : IsOpen s) {x y : ℝ} (hz : (x,y)∈s) :
    X u (x,y)=deriv (fun z => u (z,y)) x := by
  have hd := ((hu.contDiffAt (hs.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt
  exact ((hd.comp_hasDerivAt x ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))).deriv).symm

theorem Y_eq_deriv {u : Point → ℂ} {s : Set Point}
    (hu : ContDiffOn ℝ ∞ u s) (hs : IsOpen s) {x y : ℝ} (hz : (x,y)∈s) :
    Y u (x,y)=deriv (fun z => u (x,z)) y := by
  have hd := ((hu.contDiffAt (hs.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt
  exact ((hd.comp_hasDerivAt y ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))).deriv).symm

theorem XX_eq_deriv {u : Point → ℂ} {s : Set Point}
    (hu : ContDiffOn ℝ ∞ u s) (hs : IsOpen s) {x y : ℝ} (hz : (x,y)∈s) :
    X (X u) (x,y)=deriv (deriv (fun z => u (z,y))) x :=
  (dir_dir hu hs hz e₁ e₁).trans (second_horizontal hu hs hz).symm

theorem YY_eq_deriv {u : Point → ℂ} {s : Set Point}
    (hu : ContDiffOn ℝ ∞ u s) (hs : IsOpen s) {x y : ℝ} (hz : (x,y)∈s) :
    Y (Y u) (x,y)=deriv (deriv (fun z => u (x,z))) y :=
  (dir_dir hu hs hz e₂ e₂).trans (second_vertical hu hs hz).symm

#print axioms dir_dir
#print axioms XX_eq_deriv
#print axioms YY_eq_deriv

end MaassDifferential
