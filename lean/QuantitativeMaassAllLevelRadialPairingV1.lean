module

public import QuantitativeMaassAllLevelRadialOperatorV1
public import QuantitativeMaassRadialKernelPairingV1
public import QuantitativeMaassIntegralSchurPairingV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff ComplexConjugate

namespace QuantitativeMaass.AllLevel

variable (N : ℕ) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
  (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))

/-- Exact absolutely integrable pairing on the actual quotient subspace. -/
theorem radialKernelOperator_pairing (f h : AutomorphicSpace N) :
    inner ℂ h (radialKernelOperator N g hg R hR hs f)=
      ∫ p : ℍ×ℍ,star (h.val p.1)*radialPoincareKernel N g p.1 p.2*f.val p.2
        ∂(quotientMeasure N).prod (quotientMeasure N) :=
  (radialKernelData N g hg R hR hs).operator_pairing f.val h.val

/-- Real radial profiles yield self-adjoint operators on the actual
quotient Hilbert space. -/
theorem radialKernelOperator_selfAdjoint (hr : ∀ q,star (g q)=g q) :
    (radialKernelOperator N g hg R hR hs).adjoint=radialKernelOperator N g hg R hR hs := by
  let D := radialKernelData N g hg R hR hs
  have hD := D.operator_selfAdjoint (fun x y => by
    change star (radialPoincareKernel N g y x)=radialPoincareKernel N g x y
    rw [radialPoincareKernel_star N g hr,radialPoincareKernel_symm])
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f h
  change inner ℂ (D.operator f.val) h.val=inner ℂ f.val (D.operator h.val)
  exact (ContinuousLinearMap.eq_adjoint_iff _ _).mp hD.symm f.val h.val


#print axioms radialKernelOperator_pairing
#print axioms radialKernelOperator_selfAdjoint

end QuantitativeMaass.AllLevel
