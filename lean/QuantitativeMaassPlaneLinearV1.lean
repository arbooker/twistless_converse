module

public import QuantitativeMaassCauchyJetsV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem planeDerivative_linear {f g : (ℝ × ℝ) → ℂ}
    (hf : ContDiffOn ℝ ∞ f {z : ℝ × ℝ | 0<z.2})
    (hg : ContDiffOn ℝ ∞ g {z : ℝ × ℝ | 0<z.2})
    (a b : ℂ) (v z : ℝ × ℝ) (hz : 0<z.2) :
    planeDerivative v (fun w => a*f w+b*g w) z=
      a*planeDerivative v f z+b*planeDerivative v g z := by
  have hU : IsOpen {z : ℝ × ℝ | 0<z.2} := isOpen_lt continuous_const continuous_snd
  have hdf := ((hf.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt
  have hdg := ((hg.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt
  have hd : HasFDerivAt (fun w => a*f w+b*g w) _ z := (hdf.const_mul a).add (hdg.const_mul b)
  have hh := congrArg (fun A : (ℝ × ℝ) →L[ℝ] ℂ => A v) hd.fderiv
  simpa [planeDerivative] using hh

theorem planeDerivative_twice_linear {f g : (ℝ × ℝ) → ℂ}
    (hf : ContDiffOn ℝ ∞ f {z : ℝ × ℝ | 0<z.2})
    (hg : ContDiffOn ℝ ∞ g {z : ℝ × ℝ | 0<z.2})
    (a b : ℂ) (v z : ℝ × ℝ) (hz : 0<z.2) :
    planeDerivative v (planeDerivative v (fun w => a*f w+b*g w)) z=
      a*planeDerivative v (planeDerivative v f) z+b*planeDerivative v (planeDerivative v g) z := by
  have hU : IsOpen {z : ℝ × ℝ | 0<z.2} := isOpen_lt continuous_const continuous_snd
  rw [planeDerivative_congr_on hU (fun w hw => planeDerivative_linear hf hg a b v w hw) v z hz]
  exact planeDerivative_linear (planeDerivative_contDiffOn hf hU v)
    (planeDerivative_contDiffOn hg hU v) a b v z hz

theorem planeEigenEquation_linear {f g : (ℝ × ℝ) → ℂ} {lam : ℂ}
    (hf : ContDiffOn ℝ ∞ f {z : ℝ × ℝ | 0<z.2})
    (hg : ContDiffOn ℝ ∞ g {z : ℝ × ℝ | 0<z.2})
    (hef : planeEigenEquation lam f) (heg : planeEigenEquation lam g) (a b : ℂ) :
    planeEigenEquation lam (fun w => a*f w+b*g w) := by
  intro x y hy
  rw [planeDerivative_twice_linear hf hg a b (1,0) (x,y) hy,
    planeDerivative_twice_linear hf hg a b (0,1) (x,y) hy]
  linear_combination a*(hef x y hy)+b*(heg x y hy)

/-- Two smooth, horizontally analytic eigenfunctions with matching Cauchy data
on the positive axis agree throughout the upper half-plane. -/
theorem planeEigenEquation_cauchy_eq {f g : (ℝ × ℝ) → ℂ} {lam : ℂ}
    (hf : ContDiffOn ℝ ∞ f {z : ℝ × ℝ | 0<z.2})
    (hg : ContDiffOn ℝ ∞ g {z : ℝ × ℝ | 0<z.2})
    (hef : planeEigenEquation lam f) (heg : planeEigenEquation lam g)
    (haf : ∀ y : ℝ,0<y → AnalyticOnNhd ℝ (fun x => f (x,y)) univ)
    (hag : ∀ y : ℝ,0<y → AnalyticOnNhd ℝ (fun x => g (x,y)) univ)
    (hzero : ∀ y : ℝ,0<y → f (0,y)=g (0,y))
    (hone : ∀ y : ℝ,0<y → planeDerivative (1,0) f (0,y)=planeDerivative (1,0) g (0,y)) :
    ∀ x y : ℝ,0<y → f (x,y)=g (x,y) := by
  have hlin := planeEigenEquation_linear hf hg hef heg 1 (-1)
  have he : planeEigenEquation lam (fun w => f w-g w) := by
    simpa only [one_mul,neg_one_mul,←sub_eq_add_neg] using hlin
  have h1 : ∀ y : ℝ,0<y → planeDerivative (1,0) (fun w => f w-g w) (0,y)=0 := by
    intro y hy
    have hh := planeDerivative_linear hf hg 1 (-1) (1,0) (0,y) hy
    simpa only [one_mul,neg_one_mul,←sub_eq_add_neg,hone y hy,sub_self] using hh
  have hh := planeEigenEquation_zero_cauchy (hf.sub hg) he
    (fun y hy => (haf y hy).sub (hag y hy))
    (fun y hy => sub_eq_zero.mpr (hzero y hy)) h1
  intro x y hy
  exact sub_eq_zero.mp (hh x y hy)

#print axioms planeDerivative_linear
#print axioms planeDerivative_twice_linear
#print axioms planeEigenEquation_linear
#print axioms planeEigenEquation_cauchy_eq

end QuantitativeMaass
