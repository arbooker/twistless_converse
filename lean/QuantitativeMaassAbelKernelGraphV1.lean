module

public import QuantitativeMaassRadialKernelGraphV1
public import QuantitativeMaassRadialKernelLinearV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology ContDiff ComplexConjugate

namespace QuantitativeMaass

theorem coshTimeOperator_support (F : ℝ → ℂ) (B : ℝ)
    (hs : Function.support F⊆Iic B) : Function.support (coshTimeOperator F)⊆Iic B := by
  have ht : tsupport F⊆Iic B := closure_minimal hs isClosed_Iic
  have h1 : Function.support (deriv F)⊆Iic B := support_deriv_subset.trans ht
  have h2 : Function.support (deriv (deriv F))⊆Iic B :=
    support_deriv_subset.trans (tsupport_deriv_subset.trans ht)
  intro q hq
  by_contra hn
  have hd1 : deriv F q=0 := by
    by_contra h
    exact hn (h1 h)
  have hd2 : deriv (deriv F) q=0 := by
    by_contra h
    exact hn (h2 h)
  exact hq (by simp [coshTimeOperator,hd1,hd2])

theorem abelProfile_real (F : ℝ → ℂ) (hr : ∀ q,star (F q)=F q) (q : ℝ) :
    star (abelProfile F q)=abelProfile F q := by
  have hi : star (abelIntegral (deriv F) q)=abelIntegral (deriv F) q := by
    change conj (∫ s in Ioi (0:ℝ),deriv F (q+s^2))=∫ s in Ioi (0:ℝ),deriv F (q+s^2)
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards with s
    exact deriv_real_profile F hr (q+s^2)
  simp [abelProfile,star_mul,hi]
  ring

/-- The normalized geometric Abel operator takes arbitrary quotient L2
inputs into the actual Friedrichs domain and satisfies the shifted wave
identity at the level of bounded test-function operators. -/
theorem abelKernelOperator_graph (N : ℕ) [NeZero N]
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R))
    (hr : ∀ q,star (F q)=F q) (f : AutomorphicSpace N) :
    FriedrichsGraph N (abelKernelOperator N F hF hc R hR hs f)
      ((1/4:ℂ) • abelKernelOperator N F hF hc R hR hs f-
        abelKernelOperator N (coshTimeOperator F) (coshTimeOperator_smooth F hF)
          (coshTimeOperator_compact F hc) R hR (coshTimeOperator_support F _ hs) f) := by
  have hA := abelProfile_smooth F hF hc
  have hsA := abelProfile_support F _ hs
  have hH := abelProfile_smooth (coshTimeOperator F) (coshTimeOperator_smooth F hF)
    (coshTimeOperator_compact F hc)
  have hsH := abelProfile_support (coshTimeOperator F) _ (coshTimeOperator_support F _ hs)
  have hg := radialKernelOperator_graph N (abelProfile F) hA R hR hsA (abelProfile_real F hr) f
  have he := radialKernelOperator_linear N (abelProfile F) (abelProfile (coshTimeOperator F))
    (radialLaplacianProfile (abelProfile F)) hA hH (radialLaplacianProfile_smooth _ hA)
    R hR hsA hsH (radialLaplacianProfile_support _ _ hsA) (1/4:ℂ)
    (abelProfile_laplacian F hF hc) f
  rw [he] at hg
  exact hg

#print axioms coshTimeOperator_support
#print axioms abelProfile_real
#print axioms abelKernelOperator_graph

end QuantitativeMaass
