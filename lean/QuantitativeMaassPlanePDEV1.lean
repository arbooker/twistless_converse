module

public import QuantitativeMaassPlaneDerivativesV1
public import MaassFrickeCovarianceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass

def planeEigenEquation (lam : ℂ) (f : (ℝ × ℝ) → ℂ) : Prop :=
  ∀ x y : ℝ,0<y → -(y:ℂ)^2*
    (planeDerivative (1,0) (planeDerivative (1,0) f) (x,y)+
      planeDerivative (0,1) (planeDerivative (0,1) f) (x,y))=lam*f (x,y)

theorem planeDerivative_hasDerivAt_horizontal {f : (ℝ × ℝ) → ℂ}
    (hf : ContDiffOn ℝ ∞ f {z : ℝ × ℝ | 0<z.2}) (x y : ℝ) (hy : 0<y) :
    HasDerivAt (fun u => f (u,y)) (planeDerivative (1,0) f (x,y)) x := by
  have hU : IsOpen {z : ℝ × ℝ | 0<z.2} := isOpen_lt continuous_const continuous_snd
  have hd := ((hf.contDiffAt (hU.mem_nhds (show (x,y)∈{z : ℝ × ℝ | 0<z.2} from hy))).differentiableAt (by simp)).hasFDerivAt
  exact hd.comp_hasDerivAt (l:=f) x ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))

theorem planeDerivative_horizontal_vertical_twice {f : (ℝ × ℝ) → ℂ}
    (hf : ContDiffOn ℝ ∞ f {z : ℝ × ℝ | 0<z.2}) (x y : ℝ) (hy : 0<y) :
    planeDerivative (1,0) (planeDerivative (0,1) (planeDerivative (0,1) f)) (x,y)=
      planeDerivative (0,1) (planeDerivative (0,1) (planeDerivative (1,0) f)) (x,y) := by
  have hU : IsOpen {z : ℝ × ℝ | 0<z.2} := isOpen_lt continuous_const continuous_snd
  rw [planeDerivative_commute (planeDerivative_contDiffOn hf hU (0,1)) hU (0,1) (1,0) (x,y) hy]
  exact planeDerivative_congr_on hU (fun z hz => planeDerivative_commute hf hU (0,1) (1,0) z hz)
    (0,1) (x,y) hy

/-- Horizontal differentiation preserves the hyperbolic eigenfunction equation:
the height coefficient has zero horizontal derivative, and mixed derivatives
commute by proved smoothness. -/
theorem planeEigenEquation_horizontal {f : (ℝ × ℝ) → ℂ} {lam : ℂ}
    (hf : ContDiffOn ℝ ∞ f {z : ℝ × ℝ | 0<z.2}) (he : planeEigenEquation lam f) :
    planeEigenEquation lam (planeDerivative (1,0) f) := by
  intro x y hy
  have hU : IsOpen {z : ℝ × ℝ | 0<z.2} := isOpen_lt continuous_const continuous_snd
  have hxx := planeDerivative_contDiffOn (planeDerivative_contDiffOn hf hU (1,0)) hU (1,0)
  have hyy := planeDerivative_contDiffOn (planeDerivative_contDiffOn hf hU (0,1)) hU (0,1)
  have hl := ((planeDerivative_hasDerivAt_horizontal hxx x y hy).add
    (planeDerivative_hasDerivAt_horizontal hyy x y hy)).const_mul (-(y:ℂ)^2)
  have hr := (planeDerivative_hasDerivAt_horizontal hf x y hy).const_mul lam
  have heq : (fun u : ℝ => -(y:ℂ)^2*
      (planeDerivative (1,0) (planeDerivative (1,0) f) (u,y)+
        planeDerivative (0,1) (planeDerivative (0,1) f) (u,y)))=
      fun u => lam*f (u,y) := funext (fun u => he u y hy)
  simp only [Pi.add_apply] at hl
  rw [heq] at hl
  have hh := hl.unique hr
  rw [planeDerivative_horizontal_vertical_twice hf x y hy] at hh
  exact hh

/-- Connect the directional formulation to the actual hyperbolic Laplacian. -/
theorem planeEigenEquation_of_hyperbolic {f : (ℝ × ℝ) → ℂ} {lam : ℂ}
    (hf : ContDiffOn ℝ ∞ f {z : ℝ × ℝ | 0<z.2})
    (he : ∀ x y : ℝ,0<y → MaassDifferential.hyperbolic f (x,y)=lam*f (x,y)) :
    planeEigenEquation lam f := by
  intro x y hy
  have hU : IsOpen {z : ℝ × ℝ | 0<z.2} := isOpen_lt continuous_const continuous_snd
  have hh := he x y hy
  unfold MaassDifferential.hyperbolic MaassDifferential.euclidean at hh
  rw [MaassDifferential.second_horizontal hf hU hy,MaassDifferential.second_vertical hf hU hy] at hh
  rw [planeDerivative_second hf hU (1,0) (1,0) (x,y) hy,
    planeDerivative_second hf hU (0,1) (0,1) (x,y) hy]
  simpa only [MaassDifferential.H,MaassDifferential.D,MaassDifferential.e₁,MaassDifferential.e₂,
    Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_pow] using hh

#print axioms planeDerivative_hasDerivAt_horizontal
#print axioms planeDerivative_horizontal_vertical_twice
#print axioms planeEigenEquation_horizontal
#print axioms planeEigenEquation_of_hyperbolic

end QuantitativeMaass
