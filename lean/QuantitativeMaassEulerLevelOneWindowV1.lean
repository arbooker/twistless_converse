module

public import QuantitativeMaassEulerLevelOneIndependentV1
public import QuantitativeMaassCuspEigenWindowV1
public import QuantitativeConcreteGoalsV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set QuantitativeConcreteGoals

namespace QuantitativeMaass

/-- Original level-one window data as actual cusp vectors. -/
def originalLevelOneWindowVector (σ : ℕ) (t ε : ℝ) (p : maassWindow 1 σ t ε) :
    localCuspidalSpace 1 (by norm_num) := principalEulerLevelOneCuspClass p.val.1 σ p.property.2.2

theorem originalLevelOneWindowVector_independent (σ : ℕ) (t ε : ℝ) :
    LinearIndependent ℂ (originalLevelOneWindowVector σ t ε) := by
  let f : maassWindow 1 σ t ε →
      Σ r : {r : ℝ // 0≤r},MaassOriginal.EulerS 1 (.principal r.val) σ :=
    fun p => ⟨⟨p.val.1,p.property.1⟩,⟨p.val.2,p.property.2.2⟩⟩
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    exact congrArg (fun rb => (rb.1.val,rb.2.val)) hpq
  exact (originalEuler_all_level_one_cusp_independent σ).comp f hf

/-- An unconditional comparison with any actual complete cusp energy basis.
Every original level-one solution has been constructed as an independent
cusp eigenvector; no majorant, automorphy or graph input is assumed for it. -/
theorem originalLevelOneWindow_count {κ : Type*}
    (basis : HilbertBasis κ ℂ (localCuspidalSpace 1 (by norm_num))) (e : κ → ℝ)
    (henergy : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph 1 (basis j:AutomorphicSpace 1) ((e j:ℂ) • (basis j:AutomorphicSpace 1)))
    (σ : ℕ) (t ε : ℝ) :
    (maassWindow 1 σ t ε).Finite ∧
      (maassWindow 1 σ t ε).ncard≤Nat.card (principalWindowIndices e t (t+ε)) := by
  obtain ⟨hf,hc⟩ := cusp_principal_independent_window_count 1 (by norm_num) basis e henergy hgraph
    t (t+ε) (originalLevelOneWindowVector σ t ε) (originalLevelOneWindowVector_independent σ t ε)
    (fun p => p.val.1) (fun p => p.property.1) (fun p => p.property.2.1)
    (fun p => principalEulerLevelOneClass_graph p.val.1 σ p.property.2.2)
  let := hf
  exact ⟨Set.toFinite _,by simpa only [Nat.card_coe_set_eq] using hc⟩

/-- Every bounded literal original level-one window is finite. The actual
cusp spectrum is constructed internally. No analytic side condition remains. -/
theorem originalLevelOneWindow_finite (σ : ℕ) (t ε : ℝ) :
    (maassWindow 1 σ t ε).Finite := by
  obtain ⟨κ,basis,e,henergy,hgraph,_⟩ :=
    QuantitativeArithmeticMaassCuspBand.exists_cuspidal_energy_basis 1 (by norm_num)
  exact (originalLevelOneWindow_count basis e henergy hgraph σ t ε).1

#print axioms originalLevelOneWindow_finite
#print axioms originalLevelOneWindowVector_independent
#print axioms originalLevelOneWindow_count

end QuantitativeMaass
