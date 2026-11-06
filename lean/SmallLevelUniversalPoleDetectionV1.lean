module

public import QuantitativeArithmeticUniversalPoleVectorV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticUniversalPoleVector
open Complex Filter
open scoped Topology

/-- A nonzero universal principal vector cannot occur when every component
is analytic. This recovers the actual pole from the universal interface. -/
theorem IsLeadingVector.exists_pole {ι : Type*} [Fintype ι]
    {G : ℂ → ι → ℂ} {x : ℂ} {v : ι → ℂ} (hv : IsLeadingVector G x v)
    (hG : ∀ j, MeromorphicNFAt (fun z => G z j) x) :
    ∃ j, meromorphicOrderAt (fun z => G z j) x<0 := by
  classical
  by_contra! hn
  apply hv.1
  funext j
  have ha : AnalyticAt ℂ (fun z => G z j) x :=
    (hG j).meromorphicOrderAt_nonneg_iff_analyticAt.mp (hn j)
  have hh := hv.2 (fun _ i => if i=j then 1 else 0) (fun z => G z j)
    (fun _ => analyticAt_const) ha (by filter_upwards [] with z; simp)
  simpa using hh

#print axioms IsLeadingVector.exists_pole
end QuantitativeArithmeticUniversalPoleVector
