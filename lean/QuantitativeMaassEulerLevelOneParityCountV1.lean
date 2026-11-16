module

public import QuantitativeMaassEulerLevelOneWindowV1
public import QuantitativeMaassEulerLevelOneParityV1
public import QuantitativeMaassCuspParityFamilyCountV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open QuantitativeConcreteGoals

namespace QuantitativeMaass

/-- Literal original level-one window count bounded by the exact genuine
parity spectral dimension. The original family is constructed, not assumed. -/
theorem originalLevelOneWindow_parity_count {κ : Type*}
    (basis : HilbertBasis κ ℂ (localCuspidalSpace 1 (by norm_num))) (e : κ → ℝ)
    (henergy : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph 1 (basis j:AutomorphicSpace 1) ((e j:ℂ) • (basis j:AutomorphicSpace 1)))
    (σ : ℕ) (t ε : ℝ) :
    (maassWindow 1 σ t ε).Finite ∧
      (maassWindow 1 σ t ε).ncard≤
        Module.finrank ℂ (LinearMap.range (cuspWindowParity 1 (by norm_num) basis e henergy hgraph
          t (t+ε) ((-1:ℝ)^σ))) := by
  obtain ⟨hf,hc⟩ := cusp_principal_parity_family_count 1 (by norm_num) basis e henergy hgraph
    t (t+ε) ((-1:ℝ)^σ) (originalLevelOneWindowVector σ t ε)
    (originalLevelOneWindowVector_independent σ t ε) (fun p => p.val.1)
    (fun p => p.property.1) (fun p => p.property.2.1)
    (fun p => principalEulerLevelOneClass_graph p.val.1 σ p.property.2.2)
    (fun p => principalEulerLevelOneClass_parity p.val.1 σ p.property.2.2)
  let := hf
  exact ⟨Set.toFinite _,by simpa only [Nat.card_coe_set_eq] using hc⟩

#print axioms originalLevelOneWindow_parity_count

end QuantitativeMaass
