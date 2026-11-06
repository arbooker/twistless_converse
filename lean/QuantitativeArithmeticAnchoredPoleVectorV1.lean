module
public import QuantitativeArithmeticUniversalPoleVectorV1
public import QuantitativeArithmeticAnalyticGermTheoryV4
set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticAnchoredPoleVector
open Complex Filter
open scoped Topology
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticAnalyticGerm

/-- An anchored reconstruction identifies the entire universal leading
vector, and proves that its anchor coordinate cannot vanish. -/
theorem profile {ι : Type*} [Fintype ι] (G : ℂ → ι → ℂ) (x : ℂ)
    (v : ι → ℂ) (hv : IsLeadingVector G x v) (anchor : ι)
    (J : ℂ → ι → ℂ) (hJ : ∀ i, AnalyticAt ℂ (fun z => J z i) x)
    (hrow : ∀ i, HasAnalyticGerm (fun z => G z i-J z i*G z anchor) x) :
    v anchor≠0 ∧ ∀ i, v i=J x i*v anchor := by
  classical
  have hprofile (i : ι) : v i=J x i*v anchor := by
    let A : ℂ → ι → ℂ := fun z j =>
      (if j=i then 1 else 0)-J z i*(if j=anchor then 1 else 0)
    have hsum (w : ι → ℂ) (z : ℂ) : ∑ j, A z j*w j=w i-J z i*w anchor := by
      simp [A,sub_mul,Finset.sum_sub_distrib,ite_mul]
    obtain ⟨R,hR,he⟩ := hrow i
    have hA (j : ι) : AnalyticAt ℂ (fun z => A z j) x := by
      exact analyticAt_const.sub ((hJ i).mul analyticAt_const)
    have hh := hv.2 A R hA hR (by simpa only [hsum] using he)
    rw [hsum] at hh
    exact sub_eq_zero.mp hh
  refine ⟨?_,hprofile⟩
  intro hz
  apply hv.1
  funext i
  change v i=0
  rw [hprofile i,hz,mul_zero]

#print axioms profile
end QuantitativeArithmeticAnchoredPoleVector
