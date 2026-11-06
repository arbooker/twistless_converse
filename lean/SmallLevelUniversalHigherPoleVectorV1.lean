module

public import SmallLevelUniversalFactoredFirstShiftV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticUniversalPoleVector
open Complex

/-- A pole of order at least two survives multiplication by the local
parameter, and therefore has a regularized universal principal vector. -/
theorem exists_regularized_leading_vector {ι : Type*} [Fintype ι]
    (G : ℂ → ι → ℂ) (x : ℂ)
    (hG : ∀ j, MeromorphicAt (fun z => G z j) x)
    (hpole : ∃ j, meromorphicOrderAt (fun z => G z j) x<(-1:WithTop ℤ)) :
    ∃ v, IsLeadingVector (fun z j => (z-x)*G z j) x v := by
  have hf : MeromorphicAt (fun z : ℂ => z-x) x :=
    (analyticAt_id.sub analyticAt_const).meromorphicAt
  apply exists_leading_vector (fun z j => (z-x)*G z j) x
    (fun j => hf.mul (hG j))
  obtain ⟨j,hj⟩ := hpole
  refine ⟨j,?_⟩
  change meromorphicOrderAt ((fun z : ℂ => z-x)*(fun z => G z j)) x<0
  rw [meromorphicOrderAt_mul hf (hG j),meromorphicOrderAt_id_sub_const]
  lift meromorphicOrderAt (fun z => G z j) x to ℤ using hj.ne_top with n hn
  have hnlt : n< -1 := by
    change (n:WithTop ℤ)<((-1:ℤ):WithTop ℤ) at hj
    exact WithTop.coe_lt_coe.mp hj
  exact_mod_cast (show 1+n<0 by omega)

#print axioms exists_regularized_leading_vector
end QuantitativeArithmeticUniversalPoleVector
