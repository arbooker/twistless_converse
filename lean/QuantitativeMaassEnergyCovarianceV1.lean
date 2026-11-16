module

public import QuantitativeMaassEnergyDifferentialV1
public import QuantitativeMaassPoincareLaplacianV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set Filter UpperHalfPlane Matrix
open scoped Topology ContDiff MatrixGroups

namespace QuantitativeMaass
open MaassDifferential

theorem hyperbolicEnergy_eq_laplacian {u v : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hv : ContDiffOn ℝ ∞ v {Z | 0<Z.2}) {Z : Point} (hZ : 0<Z.2) :
    hyperbolicEnergy u v Z=
      (star (hyperbolic u Z)*v Z+star (u Z)*hyperbolic v Z-
        hyperbolic (fun W => star (u W)*v W) Z)/2 := by
  have h := hyperbolic_product_star hu hv hZ
  linear_combination (1/2:ℂ)*h

/-- Energy covariance under the literal integral chart, obtained from
proved differential covariance and the exact product rule. -/
theorem hyperbolicEnergy_integralCuspChart (s : SL(2,ℤ)) {u v : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hv : ContDiffOn ℝ ∞ v {Z | 0<Z.2}) {Z : Point} (hZ : 0<Z.2) :
    hyperbolicEnergy (u ∘ integralCuspChart s) (v ∘ integralCuspChart s) Z=
      hyperbolicEnergy u v (integralCuspChart s Z) := by
  have huS : ContDiffOn ℝ ∞ (fun W => star (u W)) {Z | 0<Z.2} :=
    (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn hu
  rw [hyperbolicEnergy_eq_laplacian (integralCuspChart_pullback_smooth s hu)
      (integralCuspChart_pullback_smooth s hv) hZ,
    hyperbolicEnergy_eq_laplacian hu hv (integralCuspChart_pos s Z hZ)]
  have hprod : (fun W => star ((u ∘ integralCuspChart s) W)*(v ∘ integralCuspChart s) W)=
      (fun W => star (u W)*v W) ∘ integralCuspChart s := rfl
  rw [hprod,hyperbolic_integralCuspChart s hu Z.1 Z.2 hZ,
    hyperbolic_integralCuspChart s hv Z.1 Z.2 hZ,
    hyperbolic_integralCuspChart s (huS.mul hv) Z.1 Z.2 hZ]
  rfl

theorem hyperbolicEnergy_congr_left {u u' v : Point → ℂ} {Z : Point}
    (he : u=ᶠ[𝓝 Z] u') : hyperbolicEnergy u v Z=hyperbolicEnergy u' v Z := by
  unfold hyperbolicEnergy X Y dir D
  rw [he.fderiv_eq]

theorem hyperbolicEnergy_congr_right {u v v' : Point → ℂ} {Z : Point}
    (he : v=ᶠ[𝓝 Z] v') : hyperbolicEnergy u v Z=hyperbolicEnergy u v' Z := by
  unfold hyperbolicEnergy X Y dir D
  rw [he.fderiv_eq]

theorem hyperbolicEnergy_finset_sum_right {ι : Type*} (S : Finset ι)
    (u : Point → ℂ) (v : ι → Point → ℂ)
    (hv : ∀ i∈S, ContDiffOn ℝ ∞ (v i) {Z | 0<Z.2})
    {Z : Point} (hZ : 0<Z.2) :
    hyperbolicEnergy u (fun W => ∑ i∈S, v i W) Z=∑ i∈S, hyperbolicEnergy u (v i) Z := by
  have hs : IsOpen {Z : Point | 0<Z.2} := isOpen_lt continuous_const continuous_snd
  unfold hyperbolicEnergy X Y
  rw [dir_finset_sum S v hs hv hZ e₁,dir_finset_sum S v hs hv hZ e₂]
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]

theorem hyperbolicEnergy_smooth {u v : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hv : ContDiffOn ℝ ∞ v {Z | 0<Z.2}) :
    ContDiffOn ℝ ∞ (hyperbolicEnergy u v) {Z | 0<Z.2} := by
  have hs : IsOpen {Z : Point | 0<Z.2} := isOpen_lt continuous_const continuous_snd
  have hstar (w : Point) : ContDiffOn ℝ ∞ (fun Z => star (dir w u Z)) {Z | 0<Z.2} :=
    (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn (dir_contDiffOn hu hs w)
  exact ((Complex.ofRealCLM.contDiff.comp_contDiffOn contDiffOn_snd).pow 2).mul
    (((hstar e₁).mul (dir_contDiffOn hv hs e₁)).add
      ((hstar e₂).mul (dir_contDiffOn hv hs e₂)))

#print axioms hyperbolicEnergy_integralCuspChart

end QuantitativeMaass
