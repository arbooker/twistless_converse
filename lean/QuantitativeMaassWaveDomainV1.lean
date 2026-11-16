module

public import QuantitativeMaassWaveOperatorV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Wave

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem rangeCosine_isSelfAdjoint (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hd : DenseRange A) (hi : Function.Injective A) (t : ℝ) :
    IsSelfAdjoint (rangeCosine A t) := by
  have he : rangeCosine A t*A=dampedOperator A t := by
    ext v
    exact rangeCosine_range A hA hd t v
  have hs : IsSelfAdjoint (dampedOperator A t) := cfc_predicate (dampedCosine t) A
  have hstar := congrArg star he
  rw [star_mul,hA.star_eq,hs.star_eq] at hstar
  have hcomm := (rangeCosine_commute A hA hd t).eq
  apply DFunLike.coe_injective
  funext v
  apply hi
  have h := hstar.trans (he.symm.trans hcomm)
  exact congrArg (fun B : H →L[ℂ] H => B v) h

theorem quotientWave_isSelfAdjoint (N : ℕ) (t : ℝ) : IsSelfAdjoint (quotientWave N t) :=
  rangeCosine_isSelfAdjoint _ (friedrichsResolvent_isSelfAdjoint N)
    (friedrichsResolvent_denseRange N) (friedrichsResolvent_injective N) t

/-- The constructed wave preserves the actual Friedrichs operator graph,
hence its unbounded Laplacian domain, with exact commutation. -/
theorem quotientWave_graph (N : ℕ) (t : ℝ) {x y : AutomorphicSpace N}
    (h : FriedrichsGraph N x y) :
    FriedrichsGraph N (quotientWave N t x) (quotientWave N t y) := by
  change friedrichsResolvent N (quotientWave N t x+quotientWave N t y)=quotientWave N t x
  rw [← map_add]
  have hc := congrArg (fun B : AutomorphicSpace N →L[ℂ] AutomorphicSpace N => B (x+y))
    (quotientWave_commute_resolvent N t).eq
  change quotientWave N t (friedrichsResolvent N (x+y))=
    friedrichsResolvent N (quotientWave N t (x+y)) at hc
  rw [← hc,h]

/-- In particular the literal smooth Poincaré differential pair remains a
pair in the constructed self-adjoint operator graph after wave evolution. -/
theorem quotientWave_poincareSeed_graph (N : ℕ) (t : ℝ) (u : SmoothUpperSeed) :
    (quotientWave N t (poincareSeedVector N u),
      quotientWave N t (poincareSeedVector N u.laplacian))∈(friedrichsLaplacian N).graph :=
  (friedrichsLaplacian_mem_graph N _ _).mpr
    (quotientWave_graph N t (friedrichsGraph_poincareSeed N u))

#print axioms quotientWave_isSelfAdjoint
#print axioms quotientWave_graph
#print axioms quotientWave_poincareSeed_graph

end QuantitativeMaass.Wave
