module

public import QuantitativeMaassAbelBoundaryCutoffV1
public import QuantitativeMaassAbelOperatorLinearV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass

def abelBoundaryOperator (N : ℕ) [NeZero N] (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) (a : ℝ) :
    AutomorphicSpace N →L[ℂ] AutomorphicSpace N :=
  abelKernelOperator N (abelBoundaryPart F a) (abelBoundaryPart_smooth F hF a)
    (abelBoundaryPart_compact F hc a) R hR (abelBoundaryPart_support_source F a _ hs)

/-- Removing a shrinking neighborhood of q=1 changes the geometric operator
by a term tending to zero in operator norm. All cutoff derivative constants
are derived from the given smooth compact test. -/
theorem abelBoundaryOperator_tendsto {ι : Type*} (l : Filter ι)
    (N : ℕ) [NeZero N] (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R))
    (a : ι → ℝ) (ha : ∀ i,0<a i) (ha1 : ∀ i,a i≤1) (ha0 : Tendsto a l (𝓝 0)) :
    Tendsto (fun i => abelBoundaryOperator N F hF hc R hR hs (a i)) l (𝓝 0) := by
  obtain ⟨A,hA⟩ := hc.deriv.exists_bound_of_continuous (hF.continuous_deriv (by simp))
  obtain ⟨B,hB⟩ := hc.exists_bound_of_continuous hF.continuous
  obtain ⟨D,hD,hTD⟩ := smoothTransition_deriv_bounded
  have hA0 : 0≤A := (norm_nonneg (deriv F 0)).trans (hA 0)
  have hB0 : 0≤B := (norm_nonneg (F 0)).trans (hB 0)
  have hlim : Tendsto (fun i => 1+2*a i) l (𝓝 1) := by
    simpa only [mul_zero,add_zero] using (ha0.const_mul 2).const_add 1
  exact abelKernelOperator_shrinking_support_tendsto l N (fun i => abelBoundaryPart F (a i))
    (fun i => abelBoundaryPart_smooth F hF (a i))
    (fun i => abelBoundaryPart_compact F hc (a i)) (fun _ => R) (fun _ => hR)
    (fun i => abelBoundaryPart_support_source F (a i) _ hs)
    (fun i => 1+2*a i) (2*(A+2*B*D)) (fun i => by have := ha i; linarith) hlim
    (fun i => abelBoundaryPart_support F (a i) (ha i)) (fun i q => by
      have he : 2*(A+2*B*D)/(1+2*a i-1)=(A+2*B*D)/a i := by
        rw [show 1+2*a i-1=2*a i by ring]
        field_simp
      rw [he]
      exact abelBoundaryPart_derivative_bound F hF A B D hA0 hB0 hD hA hB hTD
        (a i) (ha i) (ha1 i) q)

/-- The complementary test is identically zero in a genuine interval next
to the singular endpoint. -/
theorem abelBoundaryPart_sub_zero_near (F : ℝ → ℂ) (a : ℝ) (ha : 0<a) (ha1 : a≤1)
    (q : ℝ) (hq : 1≤q) (hqa : q≤1+a) : F q-abelBoundaryPart F a q=0 := by
  rw [abelBoundaryPart,abelBoundaryCutoff_one a ha ha1 q hq hqa,mul_one,sub_self]

#print axioms abelBoundaryOperator_tendsto
#print axioms abelBoundaryPart_sub_zero_near

end QuantitativeMaass
