module

public import QuantitativeMaassAllLevelRadialPairingV1
public import QuantitativeMaassRadialProfileCalculusV1
public import QuantitativeMaassFriedrichsGraphV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass.AllLevel

variable (N : ℕ) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
  (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
  (hr : ∀ q,star (g q)=g q)
include hr

/-- Testing an arbitrary Friedrichs-domain pair against every smooth radial
column moves the Laplacian to the literal kernel. -/
theorem radialKernelOperator_on_graph {u v : AutomorphicSpace N}
    (huv : FriedrichsGraph N u v) :
    radialKernelOperator N g hg R hR hs v=
      radialKernelOperator N (radialLaplacianProfile g) (radialLaplacianProfile_smooth g hg)
        R hR (radialLaplacianProfile_support g _ hs) u := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [radialKernelOperator_coeFn N g hg R hR hs v,
    radialKernelOperator_coeFn N (radialLaplacianProfile g) (radialLaplacianProfile_smooth g hg)
      R hR (radialLaplacianProfile_support g _ hs) u] with x hx hy
  rw [hx,hy]
  have hc := friedrichsGraph_poincareSeed N (radialSeed g hg x R hR hs)
  rw [radialSeed_laplacian_vector] at hc
  have hp := friedrichsGraph_symmetric N hc huv
  rw [radialKernel_column_inner N (radialLaplacianProfile g)
    (radialLaplacianProfile_smooth g hg) R hR (radialLaplacianProfile_support g _ hs)
    (radialLaplacianProfile_real g hr),radialKernel_column_inner N g hg R hR hs hr] at hp
  exact hp.symm

/-- The actual integral operator maps every quotient L2 vector into the
Friedrichs domain, with the integral of the differentiated kernel as Laplacian.
The proof tests against the full resolvent domain, not just a formal seed core. -/
theorem radialKernelOperator_graph (f : AutomorphicSpace N) :
    FriedrichsGraph N (radialKernelOperator N g hg R hR hs f)
      (radialKernelOperator N (radialLaplacianProfile g) (radialLaplacianProfile_smooth g hg)
        R hR (radialLaplacianProfile_support g _ hs) f) := by
  apply (friedrichsGraph_iff_adjoint N _ _).mpr
  intro u v huv
  have hK := (ContinuousLinearMap.eq_adjoint_iff _ _).mp
    (radialKernelOperator_selfAdjoint N g hg R hR hs hr).symm v f
  have hL := (ContinuousLinearMap.eq_adjoint_iff _ _).mp
    (radialKernelOperator_selfAdjoint N (radialLaplacianProfile g)
      (radialLaplacianProfile_smooth g hg) R hR (radialLaplacianProfile_support g _ hs)
      (radialLaplacianProfile_real g hr)).symm u f
  rw [← hK,← hL,radialKernelOperator_on_graph N g hg R hR hs hr huv]

#print axioms radialKernelOperator_on_graph
#print axioms radialKernelOperator_graph

end QuantitativeMaass.AllLevel
