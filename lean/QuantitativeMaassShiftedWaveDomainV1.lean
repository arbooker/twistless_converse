module

public import QuantitativeMaassShiftedWaveRangeV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Wave

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem shiftedRangeCosine_isSelfAdjoint (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hd : DenseRange A) (hi : Function.Injective A) (t : ℝ) :
    IsSelfAdjoint (shiftedRangeCosine A t) := by
  have he : shiftedRangeCosine A t*A=shiftedDampedOperator A t := by
    ext v
    exact shiftedRangeCosine_range A hA hd t v
  have hs : IsSelfAdjoint (shiftedDampedOperator A t) := cfc_predicate (shiftedDampedCosine t) A
  have hstar := congrArg star he
  rw [star_mul,hA.star_eq,hs.star_eq] at hstar
  have hcomm := (shiftedRangeCosine_commute A hA hd t).eq
  apply DFunLike.coe_injective
  funext v
  apply hi
  have h := hstar.trans (he.symm.trans hcomm)
  exact congrArg (fun B : H →L[ℂ] H => B v) h

theorem shiftedQuotientWave_isSelfAdjoint (N : ℕ) (t : ℝ) : IsSelfAdjoint (shiftedQuotientWave N t) :=
  shiftedRangeCosine_isSelfAdjoint _ (friedrichsResolvent_isSelfAdjoint N)
    (friedrichsResolvent_denseRange N) (friedrichsResolvent_injective N) t

/-- The constructed wave preserves the actual Friedrichs operator graph,
hence its unbounded Laplacian domain, with exact commutation. -/
theorem shiftedQuotientWave_graph (N : ℕ) (t : ℝ) {x y : AutomorphicSpace N}
    (h : FriedrichsGraph N x y) :
    FriedrichsGraph N (shiftedQuotientWave N t x) (shiftedQuotientWave N t y) := by
  change friedrichsResolvent N (shiftedQuotientWave N t x+shiftedQuotientWave N t y)=shiftedQuotientWave N t x
  rw [← map_add]
  have hc := congrArg (fun B : AutomorphicSpace N →L[ℂ] AutomorphicSpace N => B (x+y))
    (shiftedQuotientWave_commute_resolvent N t).eq
  change shiftedQuotientWave N t (friedrichsResolvent N (x+y))=
    friedrichsResolvent N (shiftedQuotientWave N t (x+y)) at hc
  rw [← hc,h]

/-- In particular the literal smooth Poincaré differential pair remains a
pair in the constructed self-adjoint operator graph after wave evolution. -/
theorem shiftedQuotientWave_poincareSeed_graph (N : ℕ) (t : ℝ) (u : SmoothUpperSeed) :
    (shiftedQuotientWave N t (poincareSeedVector N u),
      shiftedQuotientWave N t (poincareSeedVector N u.laplacian))∈(friedrichsLaplacian N).graph :=
  (friedrichsLaplacian_mem_graph N _ _).mpr
    (shiftedQuotientWave_graph N t (friedrichsGraph_poincareSeed N u))

#print axioms shiftedQuotientWave_isSelfAdjoint
#print axioms shiftedQuotientWave_graph
#print axioms shiftedQuotientWave_poincareSeed_graph

end QuantitativeMaass.Wave
