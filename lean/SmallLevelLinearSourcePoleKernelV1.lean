module
public import QuantitativeArithmeticUniversalPoleVectorV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelLinearSourcePoleKernel
open Complex Filter QuantitativeArithmeticUniversalPoleVector
open scoped Topology

variable {ι κ : Type*} [Fintype ι]

theorem apply_matrix (L : (κ→ℂ)→ₗ[ℂ]ℂ) (B : κ→ι→ℂ) (v : ι→ℂ) :
    L (fun i => ∑ j,B i j*v j)=∑ j,L (fun i => B i j)*v j := by
  have h := map_sum L (fun j => v j • (fun i => B i j)) Finset.univ
  have he : (∑ j,v j • (fun i => B i j))=(fun i => ∑ j,B i j*v j) := by
    funext i
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_comm]
  rw [he] at h
  simpa only [map_smul,smul_eq_mul,mul_comm] using h

/-- A row elimination operator applied to the first Taylor equation yields
an analytic row for the same universal pole vector. The weight factor has
already been absorbed into `G`; no division by that factor occurs. -/
theorem eliminated_first_source_kernel
    (G : ℂ→ι→ℂ) (x : ℂ) (v : ι→ℂ) (hv : IsLeadingVector G x v)
    (L : ℂ→((κ→ℂ)→ₗ[ℂ]ℂ)) (B : ℂ→κ→ι→ℂ) (R : ℂ→κ→ℂ)
    (hL : ∀ r : ℂ→κ→ℂ,(∀ i,AnalyticAt ℂ (fun z => r z i) x) →
      AnalyticAt ℂ (fun z => L z (r z)) x)
    (hB : ∀ i j,AnalyticAt ℂ (fun z => B z i j) x)
    (hR : ∀ i,AnalyticAt ℂ (fun z => R z i) x)
    (he : ∀ᶠ z in 𝓝[≠] x,L z (fun i => I*(∑ j,B z i j*G z j)+R z i)=0) :
    ∑ j,L x (fun i => B x i j)*v j=0 := by
  apply hv.2 (fun z j => L z (fun i => B z i j))
    (fun z => -(L z (R z))/I)
    (fun j => hL (fun z i => B z i j) (fun i => hB i j))
    ((hL R hR).neg.div_const)
  filter_upwards [he] with z hz
  have hz' : I*(∑ j,L z (fun i => B z i j)*G z j)+L z (R z)=0 := by
    have ht : (fun i => I*(∑ j,B z i j*G z j)+R z i)=
        I • (fun i => ∑ j,B z i j*G z j)+R z := rfl
    rw [ht,map_add,map_smul,smul_eq_mul,apply_matrix] at hz
    exact hz
  apply (eq_div_iff I_ne_zero).2
  linear_combination hz'

#print axioms apply_matrix
#print axioms eliminated_first_source_kernel
end SmallLevelLinearSourcePoleKernel
