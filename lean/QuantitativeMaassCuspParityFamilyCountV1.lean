module

public import QuantitativeMaassCuspEigenWindowV1
public import QuantitativeMaassSpectralWindowInvariantV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set

namespace QuantitativeMaass

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance

/-- The exact parity spectral dimension bounds every independent genuine
principal family fixed by that parity projector. -/
theorem cusp_principal_parity_family_count {κ ι : Type*} (N : ℕ) [NeZero N] (hN : 0<N)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (henergy : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (basis j:AutomorphicSpace N) ((e j:ℂ) • (basis j:AutomorphicSpace N)))
    (a b σ : ℝ) (v : ι → localCuspidalSpace N hN) (hv : LinearIndependent ℂ v) (r : ι → ℝ)
    (hr : ∀ i,0≤r i) (hwindow : ∀ i,r i∈Icc a b)
    (hvg : ∀ i,FriedrichsGraph N (v i:AutomorphicSpace N)
      (((1/4+(r i)^2:ℝ):ℂ) • (v i:AutomorphicSpace N)))
    (hparity : ∀ i,parityProjection N σ (v i:AutomorphicSpace N)=(v i:AutomorphicSpace N)) :
    Finite ι ∧ Nat.card ι≤
      Module.finrank ℂ (LinearMap.range (cuspWindowParity N hN basis e henergy hgraph a b σ)) := by
  let W := cuspPrincipalWindowSpace N hN basis e a b
  let : FiniteDimensional ℂ W := cuspPrincipalWindowSpace_finiteDimensional N hN basis e henergy hgraph a b
  let P := cuspWindowParity N hN basis e henergy hgraph a b σ
  let w : ι → W := fun i => ⟨v i,cusp_principal_eigen_mem_window N hN basis e henergy hgraph
    a b (r i) (hr i) (hwindow i) (v i) (hvg i)⟩
  have hw : LinearIndependent ℂ w := by
    apply LinearIndependent.of_comp W.subtype
    exact hv
  have hfix (i : ι) : P (w i)=w i := by
    apply Subtype.ext
    apply Subtype.ext
    exact hparity i
  let z : ι → LinearMap.range P := fun i => ⟨w i,⟨w i,hfix i⟩⟩
  have hz : LinearIndependent ℂ z := by
    apply LinearIndependent.of_comp (LinearMap.range P).subtype
    exact hw
  let : Finite ι := hz.finite
  let : Fintype ι := Fintype.ofFinite ι
  exact ⟨inferInstance,by simpa only [Nat.card_eq_fintype_card] using hz.fintype_card_le_finrank⟩

#print axioms cusp_principal_parity_family_count

end QuantitativeMaass
