module

public import QuantitativeMaassCuspTensorIntegralV1
public import QuantitativeMaassCuspHeightPairingV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology ContDiff MatrixGroups InnerProductSpace

namespace QuantitativeMaass

theorem cusp_representative_periodic (N : ℕ) (s : SL(2,ℤ))
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (y : ℝ) (hy : 0<y) :
    Function.Periodic (fun x => f.val (cuspAction s (cartesianLift (x,y)))) (N:ℝ) := by
  intro x
  change f.val (cuspAction s (cartesianLift (x+(N:ℝ),y)))=
    f.val (cuspAction s (cartesianLift (x,y)))
  rw [cartesianLift_positive (x+(N:ℝ),y) hy,cartesianLift_positive (x,y) hy]
  exact cusp_chart_periodic N s f.val f.property.2.1 y hy x

def heightLaplacianTest (g : ℝ → ℂ) (y : ℝ) : ℂ := -(y:ℂ)^2*deriv (deriv g) y

theorem heightLaplacianTest_continuous (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) :
    Continuous (heightLaplacianTest g) :=
  ((Complex.continuous_ofReal.pow 2).neg).mul
    (((contDiff_infty_iff_deriv.mp hg).2).continuous_deriv (by simp))

/-- Exact extraction of the constructed local constant term by a genuine
compact Poincare test, extended to EVERY quotient L2 state. -/
theorem cuspPeriodTest_pairing (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (a b : ℝ) (ha : 0<a)
    (hs : Function.support g⊆Icc a b) (f : AutomorphicSpace N) :
    inner ℂ (poincareSeedVector N
      ((cuspPeriodTest N (Nat.cast_pos.mpr hN) g hg a b ha hs).cuspPush s)) f=
      inner ℂ (heightTestVector _ (upperRectangle_compact 0 N a b ha) g hg.continuous)
        (cuspConstantLocal N s a b ha f) := by
  apply cuspSeed_height_pairing_of_integrals N s
    (upperRectangle 0 (2*N) a b) (upperRectangle 0 N a b)
    (upperRectangle_compact 0 (2*N) a b ha) (upperRectangle_compact 0 N a b ha)
  · exact cuspTensor_support _ _ _ _ _ _ ha
      (cuspHorizontal_support N (Nat.cast_pos.mpr hN)) hs
  · intro v hv
    exact cuspTensor_periodic_integral N a b (Nat.cast_pos.mpr hN) ha g hg.continuous
      (fun Z => v.val (cuspAction s Z)) (hv.comp (cuspAction_continuous s))
      (cusp_representative_periodic N s v)

/-- Exact test-Laplacian extraction. Horizontal cancellation has been
proved and the equality holds on the full quotient Hilbert space. -/
theorem cuspPeriodTest_laplacian_pairing (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (a b : ℝ) (ha : 0<a)
    (hs : Function.support g⊆Icc a b) (f : AutomorphicSpace N) :
    inner ℂ (poincareSeedVector N
      ((cuspPeriodTest N (Nat.cast_pos.mpr hN) g hg a b ha hs).laplacian.cuspPush s)) f=
      inner ℂ (heightTestVector _ (upperRectangle_compact 0 N a b ha)
        (heightLaplacianTest g) (heightLaplacianTest_continuous g hg))
        (cuspConstantLocal N s a b ha f) := by
  apply cuspSeed_height_pairing_of_integrals N s
    (upperRectangle 0 (2*N) a b) (upperRectangle 0 N a b)
    (upperRectangle_compact 0 (2*N) a b ha) (upperRectangle_compact 0 N a b ha)
  · apply closure_minimal _ (upperRectangle_compact 0 (2*N) a b ha).isClosed
    exact (upperLaplacian_support _).trans
      (cuspTensor_support _ _ _ _ _ _ ha (cuspHorizontal_support N (Nat.cast_pos.mpr hN)) hs)
  · intro v hv
    exact cuspTensor_laplacian_periodic_integral N a b (Nat.cast_pos.mpr hN) ha g hg
      (fun Z => v.val (cuspAction s Z)) (hv.comp (cuspAction_continuous s))
      (cusp_representative_periodic N s v)

#print axioms cuspPeriodTest_pairing
#print axioms cuspPeriodTest_laplacian_pairing

end QuantitativeMaass
