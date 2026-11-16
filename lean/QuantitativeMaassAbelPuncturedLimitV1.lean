module

public import QuantitativeMaassAbelBoundaryLimitV1

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- The actual geometric operator of the test with a neighborhood of q=1
removed. This is defined from its kernel, rather than as an operator difference. -/
def abelPuncturedOperator (N : ℕ) [NeZero N] (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) (a : ℝ) :
    AutomorphicSpace N →L[ℂ] AutomorphicSpace N :=
  abelKernelOperator N (fun q => F q-abelBoundaryPart F a q)
    (hF.sub (abelBoundaryPart_smooth F hF a)) (hc.sub (abelBoundaryPart_compact F hc a))
    R hR (support_sub_Iic F (abelBoundaryPart F a) _ hs (abelBoundaryPart_support_source F a _ hs))

theorem abelPuncturedOperator_eq_sub (N : ℕ) [NeZero N]
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) (a : ℝ) :
    abelPuncturedOperator N F hF hc R hR hs a=
      abelKernelOperator N F hF hc R hR hs-abelBoundaryOperator N F hF hc R hR hs a :=
  abelKernelOperator_sub N F (abelBoundaryPart F a) hF (abelBoundaryPart_smooth F hF a)
    hc (abelBoundaryPart_compact F hc a) R hR hs (abelBoundaryPart_support_source F a _ hs)

/-- Every original smooth compact q-test operator is an operator-norm limit
of actual test operators whose time tests vanish near zero. -/
theorem abelPuncturedOperator_tendsto {ι : Type*} (l : Filter ι)
    (N : ℕ) [NeZero N] (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R))
    (a : ι → ℝ) (ha : ∀ i,0<a i) (ha1 : ∀ i,a i≤1) (ha0 : Tendsto a l (𝓝 0)) :
    Tendsto (fun i => abelPuncturedOperator N F hF hc R hR hs (a i)) l
      (𝓝 (abelKernelOperator N F hF hc R hR hs)) := by
  apply (tendsto_iff_norm_sub_tendsto_zero
    (f := fun i => abelPuncturedOperator N F hF hc R hR hs (a i))
    (b := abelKernelOperator N F hF hc R hR hs)).mpr
  have he : (fun i => ‖abelPuncturedOperator N F hF hc R hR hs (a i)-
      abelKernelOperator N F hF hc R hR hs‖)=
      (fun i => ‖abelBoundaryOperator N F hF hc R hR hs (a i)‖) := by
    funext i
    rw [abelPuncturedOperator_eq_sub]
    have hid : (abelKernelOperator N F hF hc R hR hs-
        abelBoundaryOperator N F hF hc R hR hs (a i))-
        abelKernelOperator N F hF hc R hR hs=
        -abelBoundaryOperator N F hF hc R hR hs (a i) := by abel
    rw [hid]
    exact norm_neg (abelBoundaryOperator N F hF hc R hR hs (a i))
  rw [he]
  exact (tendsto_zero_iff_norm_tendsto_zero
    (f := fun i => abelBoundaryOperator N F hF hc R hR hs (a i))).mp
      (abelBoundaryOperator_tendsto l N F hF hc R hR hs a ha ha1 ha0)

#print axioms abelPuncturedOperator_eq_sub
#print axioms abelPuncturedOperator_tendsto

end QuantitativeMaass
