module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 20000

@[expose] public section

open Set Filter
open scoped Topology ContDiff

namespace MaassDifferential

abbrev Point := ℝ × ℝ

noncomputable def D (u : Point → ℂ) := fderiv ℝ u
noncomputable def H (u : Point → ℂ) := fderiv ℝ (D u)

theorem second_curve {u : Point → ℂ} {s : Set Point}
    (hu : ContDiffOn ℝ ∞ u s) (hs : IsOpen s)
    {g g' : ℝ → Point} {t : ℝ} {g'' : Point}
    (hg : ∀ᶠ z in 𝓝 t, HasDerivAt g (g' z) z)
    (hg' : HasDerivAt g' g'' t) (hm : g t∈s) :
    deriv (deriv (fun z => u (g z))) t =
      H u (g t) (g' t) (g' t)+D u (g t) g'' := by
  have hgt : HasDerivAt g (g' t) t := hg.self_of_nhds
  have hmem : ∀ᶠ z in 𝓝 t, g z∈s :=
    hgt.continuousAt.preimage_mem_nhds (hs.mem_nhds hm)
  have hu1 : ∀ w∈s, HasFDerivAt u (D u w) w := fun w hw =>
    ((hu.contDiffAt (hs.mem_nhds hw)).differentiableAt (by simp)).hasFDerivAt
  have huD : ContDiffOn ℝ 1 (D u) s :=
    hu.fderiv_of_isOpen hs (by simp)
  have hD : HasFDerivAt (D u) (H u (g t)) (g t) :=
    ((huD.contDiffAt (hs.mem_nhds hm)).differentiableAt (by norm_num)).hasFDerivAt
  have he : deriv (fun z => u (g z)) =ᶠ[𝓝 t] (fun z => D u (g z) (g' z)) := by
    filter_upwards [hg,hmem] with z hz hzs
    exact ((hu1 (g z) hzs).comp_hasDerivAt z hz).deriv
  have hd := (hD.comp_hasDerivAt t hgt).clm_apply hg'
  rw [he.deriv_eq]
  exact hd.deriv

def e₁ : Point := (1,0)
def e₂ : Point := (0,1)

theorem second_horizontal {u : Point → ℂ} {s : Set Point}
    (hu : ContDiffOn ℝ ∞ u s) (hs : IsOpen s) {x y : ℝ} (hz : (x,y)∈s) :
    deriv (deriv (fun z => u (z,y))) x = H u (x,y) e₁ e₁ := by
  have h := second_curve hu hs (g := fun z => (z,y)) (g' := fun _ => e₁)
    (g'' := 0)
    (Eventually.of_forall (fun z => (hasDerivAt_id z).prodMk (hasDerivAt_const z y)))
    (hasDerivAt_const x e₁) hz
  simpa only [map_zero,add_zero] using h

theorem second_vertical {u : Point → ℂ} {s : Set Point}
    (hu : ContDiffOn ℝ ∞ u s) (hs : IsOpen s) {x y : ℝ} (hz : (x,y)∈s) :
    deriv (deriv (fun z => u (x,z))) y = H u (x,y) e₂ e₂ := by
  have h := second_curve hu hs (g := fun z => (x,z)) (g' := fun _ => e₂)
    (g'' := 0)
    (Eventually.of_forall (fun z => (hasDerivAt_const z x).prodMk (hasDerivAt_id z)))
    (hasDerivAt_const y e₂) hz
  simpa only [map_zero,add_zero] using h

#print axioms second_curve
#print axioms second_horizontal
#print axioms second_vertical

end MaassDifferential
