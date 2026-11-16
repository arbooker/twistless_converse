module

public import QuantitativeMaassLaplacianLinearV1
public import QuantitativeMaassLaplacianSupportV1
public import QuantitativeMaassEulerWaveEquationV1
public import Mathlib.LinearAlgebra.Eigenspace.Basic

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MaassDifferential
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Smooth functions on the physical upper half-plane, represented by zero
extension outside that domain. No boundary smoothness is required. -/
def smoothUpperSpace : Submodule ℂ ((ℝ×ℝ) → ℂ) where
  carrier := {f | ContDiffOn ℝ ∞ f {z | 0<z.2} ∧ ∀ z, z.2≤0 → f z=0}
  zero_mem' := ⟨contDiffOn_const,fun _ _ => rfl⟩
  add_mem' := by
    intro f g hf hg
    exact ⟨hf.1.add hg.1,fun z hz => by simp [hf.2 z hz,hg.2 z hz]⟩
  smul_mem' := by
    intro c f hf
    exact ⟨contDiffOn_const.smul hf.1,fun z hz => by simp [hf.2 z hz]⟩

/-- The literal hyperbolic differential expression is a linear endomorphism
on the actual smooth function space. -/
def smoothUpperLaplacian : Module.End ℂ smoothUpperSpace where
  toFun f := ⟨fun z => if 0<z.2 then hyperbolic f z else 0,by
    constructor
    · apply (hyperbolic_contDiffOn f.property.1).congr
      intro z hz
      exact ite_eq_left hz
    · intro z hz
      exact ite_eq_right (not_lt.mpr hz)⟩
  map_add' f g := by
    apply Subtype.ext
    funext z
    by_cases hz : 0<z.2
    · simp only [hz,ite_true,Submodule.coe_add,Pi.add_apply]
      exact hyperbolic_add_smooth f.property.1 g.property.1 hz
    · simp [hz]
  map_smul' c f := by
    apply Subtype.ext
    funext z
    by_cases hz : 0<z.2
    · simp only [hz,ite_true,Submodule.coe_smul,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
      exact hyperbolic_const_smul c f z
    · simp [hz]

def principalEulerSmooth {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ : ℕ) : smoothUpperSpace :=
  ⟨principalEulerWave b r σ,principalEulerWave_contDiffOn hb r σ,fun z hz => by
    simp [principalEulerWave,Real.sqrt_eq_zero_of_nonpos hz]⟩

theorem principalEulerSmooth_eigen {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ : ℕ) :
    smoothUpperLaplacian (principalEulerSmooth hb r σ)=((1/4+r^2:ℝ):ℂ) • principalEulerSmooth hb r σ := by
  apply Subtype.ext
  funext z
  by_cases hz : 0<z.2
  · change (if 0<z.2 then hyperbolic (principalEulerWave b r σ) z else 0)=_
    rw [ite_eq_left hz]
    exact principalEulerWave_hyperbolic hb r σ z.1 z.2 hz
  · have hw : principalEulerWave b r σ z=0 := (principalEulerSmooth hb r σ).property.2 z (le_of_not_gt hz)
    simp [smoothUpperLaplacian,principalEulerSmooth,hz,hw]

/-- Distinct Laplace eigenspaces of these actual smooth functions are
independent; no Hilbert orthogonality or automorphy is being assumed. -/
theorem smoothUpper_eigenspaces_independent : iSupIndep smoothUpperLaplacian.eigenspace :=
  smoothUpperLaplacian.eigenspaces_iSupIndep

#print axioms smoothUpperLaplacian
#print axioms principalEulerSmooth_eigen
#print axioms smoothUpper_eigenspaces_independent

end QuantitativeMaass
