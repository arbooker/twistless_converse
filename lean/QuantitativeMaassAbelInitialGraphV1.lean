module

public import QuantitativeMaassAbelStrongInitialV1
public import QuantitativeMaassRadialKernelCommuteV1

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem abelNormalizedProfile_real (R q : ℝ) :
    star (abelNormalizedProfile R q)=abelNormalizedProfile R q :=
  abelProfile_real _ (abelNormalizedTest_real R) q

/-- The normalized approximation preserves actual Friedrichs graph pairs. -/
theorem abelNormalizedOperator_graph (N : ℕ) [NeZero N] (R : ℝ) (hR : 0<R)
    {f h : AutomorphicSpace N} (hfh : FriedrichsGraph N f h) :
    FriedrichsGraph N (abelNormalizedOperator N R hR f) (abelNormalizedOperator N R hR h) := by
  have hg := radialKernelOperator_graph N (abelNormalizedProfile R)
    (abelNormalizedProfile_smooth R hR) R hR.le (abelNormalizedProfile_support R hR)
    (abelNormalizedProfile_real R) f
  have he := radialKernelOperator_on_graph N (abelNormalizedProfile R)
    (abelNormalizedProfile_smooth R hR) R hR.le (abelNormalizedProfile_support R hR)
    (abelNormalizedProfile_real R) hfh
  rw [← he] at hg
  exact hg

theorem abelNormalizedOperator_commute_wave (N : ℕ) [NeZero N] (R : ℝ) (hR : 0<R) (t : ℝ) :
    Commute (abelNormalizedOperator N R hR) (Wave.shiftedQuotientWave N t) :=
  radialKernelOperator_commute_wave N (abelNormalizedProfile R) (abelNormalizedProfile_smooth R hR)
    R hR.le (abelNormalizedProfile_support R hR) (abelNormalizedProfile_real R) t

/-- Approximation is strong in both components of every actual graph pair,
so no domain regularity is lost when using the kernels in wave uniqueness. -/
theorem abelNormalizedOperator_graph_tendsto {ι : Type*} (l : Filter ι) [l.IsCountablyGenerated]
    (N : ℕ) [NeZero N] (R : ι → ℝ) (hR : ∀ i,0<R i) (hlim : Tendsto R l (𝓝 0))
    {f h : AutomorphicSpace N} (hfh : FriedrichsGraph N f h) :
    (∀ i,FriedrichsGraph N (abelNormalizedOperator N (R i) (hR i) f)
      (abelNormalizedOperator N (R i) (hR i) h)) ∧
    Tendsto (fun i => (abelNormalizedOperator N (R i) (hR i) f,
      abelNormalizedOperator N (R i) (hR i) h)) l (𝓝 (f,h)) :=
  ⟨fun i => abelNormalizedOperator_graph N (R i) (hR i) hfh,
    (abelNormalizedOperator_tendsto l N R hR hlim f).prodMk_nhds
      (abelNormalizedOperator_tendsto l N R hR hlim h)⟩

#print axioms abelNormalizedOperator_graph
#print axioms abelNormalizedOperator_commute_wave
#print axioms abelNormalizedOperator_graph_tendsto

end QuantitativeMaass
