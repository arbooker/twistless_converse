module

public import QuantitativeMaassAbelInitialGraphV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Testing against all actual smooth compact Poincare seeds suffices for
the full Friedrichs graph. Radial smoothing first gives full-domain graph
pairs; strong approximate identity and closedness remove the smoothing. -/
theorem friedrichsGraph_of_seed_pairings (N : ℕ) [NeZero N] (f h : AutomorphicSpace N)
    (hweak : ∀ u : SmoothUpperSeed,inner ℂ (poincareSeedVector N u.laplacian) f=
      inner ℂ (poincareSeedVector N u) h) : FriedrichsGraph N f h := by
  have happrox (R : ℝ) (hR : 0<R) :
      FriedrichsGraph N (abelNormalizedOperator N R hR f) (abelNormalizedOperator N R hR h) := by
    let g := abelNormalizedProfile R
    have hg := abelNormalizedProfile_smooth R hR
    have hs := abelNormalizedProfile_support R hR
    have hr := abelNormalizedProfile_real R
    have hgraph := radialKernelOperator_graph N g hg R hR.le hs hr f
    have he : radialKernelOperator N (radialLaplacianProfile g) (radialLaplacianProfile_smooth g hg)
        R hR.le (radialLaplacianProfile_support g _ hs) f=
      radialKernelOperator N g hg R hR.le hs h := by
      apply Subtype.ext
      apply Lp.ext
      filter_upwards [radialKernelOperator_coeFn N (radialLaplacianProfile g)
        (radialLaplacianProfile_smooth g hg) R hR.le (radialLaplacianProfile_support g _ hs) f,
        radialKernelOperator_coeFn N g hg R hR.le hs h] with x hx hy
      rw [hx,hy]
      have hh := hweak (radialSeed g hg x R hR.le hs)
      rw [radialSeed_laplacian_vector,radialKernel_column_inner N (radialLaplacianProfile g)
        (radialLaplacianProfile_smooth g hg) R hR.le (radialLaplacianProfile_support g _ hs)
        (radialLaplacianProfile_real g hr),radialKernel_column_inner N g hg R hR.le hs hr] at hh
      exact hh
    rw [he] at hgraph
    exact hgraph
  let R : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hR (n : ℕ) : 0<R n := by dsimp [R]; positivity
  have ht : Tendsto R atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  exact (friedrichsGraph_closed N).mem_of_tendsto
    ((abelNormalizedOperator_tendsto atTop N R hR ht f).prodMk_nhds
      (abelNormalizedOperator_tendsto atTop N R hR ht h))
    (Eventually.of_forall (fun n => happrox (R n) (hR n)))

#print axioms friedrichsGraph_of_seed_pairings

end QuantitativeMaass
