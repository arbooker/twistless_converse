module

public import QuantitativeMaassFiniteSpectralSpaceV1
public import QuantitativeMaassWaveSeparationV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set
open scoped Topology

namespace QuantitativeMaass

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance

variable {κ ι : Type*} (N : ℕ) (hN : 0<N)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (henergy : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (basis j:AutomorphicSpace N) ((e j:ℂ) • (basis j:AutomorphicSpace N)))

include basis henergy hgraph

/-- Every actual principal cusp eigenvector in an interval lies in the finite
span of the corresponding entries of a complete cusp energy basis. -/
theorem cusp_principal_eigen_mem_window (a b r : ℝ) (hr : 0≤r) (hwindow : r∈Icc a b)
    (v : localCuspidalSpace N hN)
    (hv : FriedrichsGraph N (v:AutomorphicSpace N) (((1/4+r^2:ℝ):ℂ) • (v:AutomorphicSpace N))) :
    v∈cuspPrincipalWindowSpace N hN basis e a b := by
  have ho := basis.orthonormal.comp_linearIsometry (localCuspidalSpace N hN).subtypeₗᵢ
  apply hilbertBasis_mem_finite_span basis _
    (principalWindowIndices_finite N hN _ ho (fun j => (basis j).property) e henergy hgraph a b)
  intro i hi
  rw [basis.repr_apply_apply]
  change inner ℂ (basis i:AutomorphicSpace N) (v:AutomorphicSpace N)=0
  have hne : e i≠1/4+r^2 := by
    intro heq
    apply hi
    change 1/4≤e i ∧ Real.sqrt (e i-1/4)∈Icc a b
    rw [heq]
    constructor
    · nlinarith [sq_nonneg r]
    · simpa only [add_sub_cancel_left,Real.sqrt_sq hr] using hwindow
  simpa only [ContinuousLinearMap.id_apply] using
    wave_commuting_energy_coefficient_zero N (ContinuousLinearMap.id ℂ _)
      (fun _ => by ext; rfl) (basis i) v (e i) (1/4+r^2) (henergy i)
      (by positivity) (hgraph i) hv hne

/-- Finiteness and the exact spectral-band dimension bound for any independent
family of genuine cusp eigenvectors, without assuming orthogonality. -/
theorem cusp_principal_independent_window_count (a b : ℝ)
    (v : ι → localCuspidalSpace N hN) (hv : LinearIndependent ℂ v) (r : ι → ℝ)
    (hr : ∀ i,0≤r i) (hwindow : ∀ i,r i∈Icc a b)
    (hvg : ∀ i,FriedrichsGraph N (v i:AutomorphicSpace N)
      (((1/4+(r i)^2:ℝ):ℂ) • (v i:AutomorphicSpace N))) :
    Finite ι ∧ Nat.card ι≤Nat.card (principalWindowIndices e a b) := by
  let W := cuspPrincipalWindowSpace N hN basis e a b
  let : FiniteDimensional ℂ W := cuspPrincipalWindowSpace_finiteDimensional N hN basis e henergy hgraph a b
  let w : ι → W := fun i => ⟨v i,cusp_principal_eigen_mem_window N hN basis e henergy hgraph
    a b (r i) (hr i) (hwindow i) (v i) (hvg i)⟩
  have hw : LinearIndependent ℂ w := by
    apply LinearIndependent.of_comp W.subtype
    exact hv
  let : Finite ι := hw.finite
  let : Fintype ι := Fintype.ofFinite ι
  refine ⟨inferInstance,?_⟩
  rw [Nat.card_eq_fintype_card,←cuspPrincipalWindowSpace_finrank N hN basis e henergy hgraph a b]
  exact hw.fintype_card_le_finrank

#print axioms cusp_principal_eigen_mem_window
#print axioms cusp_principal_independent_window_count

end QuantitativeMaass
