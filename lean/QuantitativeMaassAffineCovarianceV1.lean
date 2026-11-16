module

public import MaassFrickeSmoothV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

/-- Positive affine hyperbolic isometries, in actual Cartesian coordinates. -/
def affineChart (a b : ℝ) (Z : Point) : Point := (a*Z.1+b,a*Z.2)

theorem affineChart_smooth (a b : ℝ) : ContDiff ℝ ∞ (affineChart a b) := by
  exact ((contDiff_const.mul contDiff_fst).add contDiff_const).prodMk
    (contDiff_const.mul contDiff_snd)

theorem affine_pullback_smooth {u : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2}) {a : ℝ} (ha : 0<a) (b : ℝ) :
    ContDiffOn ℝ ∞ (u ∘ affineChart a b) {Z | 0<Z.2} :=
  hu.comp (affineChart_smooth a b).contDiffOn (fun _ hZ => mul_pos ha hZ)

theorem euclidean_affine {u : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2}) {a : ℝ} (ha : 0<a)
    (b x y : ℝ) (hy : 0<y) :
    euclidean (u ∘ affineChart a b) (x,y) =
      a^2 • euclidean u (affineChart a b (x,y)) := by
  have hs : IsOpen {Z : Point | 0<Z.2} := isOpen_lt continuous_const continuous_snd
  have hz : affineChart a b (x,y) ∈ {Z : Point | 0<Z.2} := mul_pos ha hy
  have hx := second_curve hu hs (g := fun z => affineChart a b (z,y))
    (g' := fun _ => (a,0)) (g'' := 0)
    (Eventually.of_forall fun z => by simpa [affineChart] using
      (((hasDerivAt_id z).const_mul a).add_const b).prodMk (hasDerivAt_const z (a*y)))
    (hasDerivAt_const x (a,0)) hz
  have hyy := second_curve hu hs (g := fun z => affineChart a b (x,z))
    (g' := fun _ => (0,a)) (g'' := 0)
    (Eventually.of_forall fun z => by simpa [affineChart] using
      (hasDerivAt_const z (a*x+b)).prodMk ((hasDerivAt_id z).const_mul a))
    (hasDerivAt_const y (0,a)) hz
  change deriv (deriv (fun z => u (affineChart a b (z,y)))) x +
    deriv (deriv (fun z => u (affineChart a b (x,z)))) y = _
  rw [hx,hyy,map_zero,add_zero,add_zero]
  have h1 : (a,0)=a•e₁ := by ext <;> simp [e₁]
  have h2 : (0,a)=a•e₂ := by ext <;> simp [e₂]
  rw [h1,h2]
  simp only [map_smul,smul_apply,smul_smul,← smul_add,pow_two]
  congr 1
  exact (congrArg₂ (·+·) (second_horizontal hu hs hz)
    (second_vertical hu hs hz)).symm

theorem hyperbolic_affine {u : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2}) {a : ℝ} (ha : 0<a)
    (b x y : ℝ) (hy : 0<y) :
    hyperbolic (u ∘ affineChart a b) (x,y) =
      hyperbolic u (affineChart a b (x,y)) := by
  unfold hyperbolic
  rw [euclidean_affine hu ha b x y hy,smul_smul]
  congr 1
  simp only [affineChart]
  ring

#print axioms hyperbolic_affine

end QuantitativeMaass
