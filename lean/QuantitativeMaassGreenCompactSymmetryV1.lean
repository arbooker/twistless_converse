module

public import QuantitativeMaassGreenCompactV1
public import QuantitativeMaassLaplacianSupportV1
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

theorem hyperbolic_zero_of_notMem_tsupport {u : Point → ℂ} {Z : Point}
    (hZ : Z∉tsupport u) : hyperbolic u Z=0 := by
  have h := hyperbolic_congr_eventually (notMem_tsupport_iff_eventuallyEq.mp hZ)
  simpa [hyperbolic,euclidean] using h

/-- The same Green formula with the compact test in the second slot. Here
its normal derivatives vanish on the enclosing rectangle, so boundary
products vanish although the first function need not vanish there. -/
theorem green_compact_right {u v : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hv : ContDiffOn ℝ ∞ v {Z | 0<Z.2})
    (hc : HasCompactSupport v) (hp : ∀ Z∈tsupport v, 0<Z.2) :
    (∫ Z : Point, star (u Z)*hyperbolic v Z/(Z.2:ℂ)^2)=
      ∫ Z : Point, star (X u Z)*X v Z+star (Y u Z)*Y v Z := by
  obtain ⟨l,r,a,b,hlr,ha,hab,hK⟩ := compact_upper_rectangle hc hp
  have hz (Z : Point) (hZ : Z∉Ioo l r ×ˢ Ioo a b) : X v Z=0 ∧ Y v Z=0 := by
    have hd := fderiv_of_notMem_tsupport ℝ (fun h => hZ (hK h))
    simp [X,Y,dir,D,hd]
  have hg := green_rectangle_boundary l r a b hlr ha hab hu hv
    (fun y => by rw [(hz (l,y) (by simp)).1,mul_zero])
    (fun y => by rw [(hz (r,y) (by simp)).1,mul_zero])
    (fun x => by rw [(hz (x,a) (by simp)).2,mul_zero])
    (fun x => by rw [(hz (x,b) (by simp)).2,mul_zero])
  have hn (Z : Point) (hZ : Z∉Ioc l r ×ˢ Ioc a b) : Z∉tsupport v := by
    intro h
    exact hZ ⟨⟨(hK h).1.1,(hK h).1.2.le⟩,⟨(hK h).2.1,(hK h).2.2.le⟩⟩
  have he (Z : Point) (hZ : Z∉Ioc l r ×ˢ Ioc a b) :
      star (X u Z)*X v Z+star (Y u Z)*Y v Z=0 := by
    have hd := fderiv_of_notMem_tsupport ℝ (hn Z hZ)
    simp [X,Y,dir,D,hd]
  have hl (Z : Point) (hZ : Z∉Ioc l r ×ˢ Ioc a b) :
      star (u Z)*hyperbolic v Z/(Z.2:ℂ)^2=0 := by
    rw [hyperbolic_zero_of_notMem_tsupport (hn Z hZ),mul_zero,zero_div]
  unfold greenRectangle at hg
  rw [Measure.prod_restrict] at hg
  change (∫ Z in Ioc l r ×ˢ Ioc a b, _) = ∫ Z in Ioc l r ×ˢ Ioc a b, _ at hg
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hl,
    setIntegral_eq_integral_of_forall_compl_eq_zero he] at hg
  exact hg

/-- Symmetry of the literal ambient differential expression against an
arbitrary smooth function, with only the first test compactly supported. -/
theorem green_compact_symmetric {u v : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hv : ContDiffOn ℝ ∞ v {Z | 0<Z.2})
    (hc : HasCompactSupport u) (hp : ∀ Z∈tsupport u, 0<Z.2) :
    (∫ Z : Point, star (u Z)*hyperbolic v Z/(Z.2:ℂ)^2)=
      ∫ Z : Point, star (hyperbolic u Z)*v Z/(Z.2:ℂ)^2 := by
  have h := congrArg star (green_compact_right hv hu hc hp)
  simp only [← starRingEnd_apply,← integral_conj] at h
  have h' : (∫ Z : Point, star (hyperbolic u Z)*v Z/(Z.2:ℂ)^2)=
      ∫ Z : Point, star (X u Z)*X v Z+star (Y u Z)*Y v Z := by
    convert h using 1 <;> congr 1 <;> funext Z <;>
      simp [mul_comm]
  exact (green_compact hu hv hc hp).trans h'.symm

#print axioms green_compact_symmetric

end QuantitativeMaass
