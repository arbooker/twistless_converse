module

public import QuantitativeMaassFiniteSpectralSpaceV1
public import QuantitativeMaassWaveSeparationV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open AsymptoticCongruenceStrip
open scoped Topology InnerProductSpace

namespace QuantitativeMaass

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance

/-- A cusp-preserving operator commuting with the genuine wave preserves
every finite principal spectral window. This uses actual energy separation
and completeness of the constructed cusp basis. -/
theorem wave_commuting_preserves_cuspPrincipalWindowSpace {κ : Type*}
    (N : ℕ) (hN : 0<N)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (henergy : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (basis j:AutomorphicSpace N) ((e j:ℂ) • (basis j:AutomorphicSpace N)))
    (U : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (hUc : ∀ x,x∈localCuspidalSpace N hN → U x∈localCuspidalSpace N hN)
    (hU : ∀ t,Commute U (Wave.shiftedQuotientWave N t))
    (a b : ℝ) (x : localCuspidalSpace N hN)
    (hx : x∈cuspPrincipalWindowSpace N hN basis e a b) :
    U.toLinearMap.restrict hUc x∈cuspPrincipalWindowSpace N hN basis e a b := by
  let S := principalWindowIndices e a b
  let L := U.toLinearMap.restrict hUc
  have ho : Orthonormal ℂ (fun j => (basis j:AutomorphicSpace N)) :=
    basis.orthonormal.comp_linearIsometry (localCuspidalSpace N hN).subtypeₗᵢ
  have hS : S.Finite := principalWindowIndices_finite N hN _ ho (fun j => (basis j).property)
    e henergy hgraph a b
  have hgen (j : S) : L (basis j.val)∈Submodule.span ℂ (Set.range (fun i : S => basis i.val)) := by
    apply hilbertBasis_mem_finite_span basis S hS
    intro i hi
    rw [basis.repr_apply_apply]
    change inner ℂ (basis i:AutomorphicSpace N) (U (basis j.val:AutomorphicSpace N))=0
    apply wave_commuting_energy_coefficient_zero N U hU _ _ _ _ (henergy i) (henergy j.val)
      (hgraph i) (hgraph j.val)
    intro heq
    apply hi
    change 1/4≤e i ∧ Real.sqrt (e i-1/4)∈Icc a b
    rw [heq]
    exact j.property
  change L x∈Submodule.span ℂ (Set.range (fun i : S => basis i.val))
  change x∈Submodule.span ℂ (Set.range (fun i : S => basis i.val)) at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j,rfl⟩ := hy
    exact hgen j
  | zero => simpa only [map_zero] using (Submodule.zero_mem (Submodule.span ℂ (Set.range (fun i : S => basis i.val))))
  | add y z _ _ hy hz => simpa only [map_add] using Submodule.add_mem _ hy hz
  | smul c y _ hy => simpa only [map_smul] using Submodule.smul_mem _ c hy

/-- The genuine reflection parity projection restricted to the cusp space. -/
def cuspParityOperator (N : ℕ) (hN : 0<N) (σ : ℝ) :
    localCuspidalSpace N hN →ₗ[ℂ] localCuspidalSpace N hN :=
  (parityProjection N σ).toLinearMap.restrict
    (fun x hx => parityProjection_mem_localCuspidalSpace N hN σ x hx)

theorem cuspParityOperator_preserves_window {κ : Type*}
    (N : ℕ) [NeZero N] (hN : 0<N)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (henergy : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (basis j:AutomorphicSpace N) ((e j:ℂ) • (basis j:AutomorphicSpace N)))
    (a b σ : ℝ) (x : localCuspidalSpace N hN)
    (hx : x∈cuspPrincipalWindowSpace N hN basis e a b) :
    cuspParityOperator N hN σ x∈cuspPrincipalWindowSpace N hN basis e a b := by
  exact wave_commuting_preserves_cuspPrincipalWindowSpace N hN basis e henergy hgraph
    (parityProjection N σ) (fun x hx => parityProjection_mem_localCuspidalSpace N hN σ x hx)
    (fun t => parityProjection_commute N σ _ (reflectionIsometry_wave_commute N t)) a b x hx

/-- Actual parity projection as an endomorphism of the finite spectral band. -/
def cuspWindowParity {κ : Type*} (N : ℕ) [NeZero N] (hN : 0<N)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (henergy : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (basis j:AutomorphicSpace N) ((e j:ℂ) • (basis j:AutomorphicSpace N)))
    (a b σ : ℝ) : cuspPrincipalWindowSpace N hN basis e a b →ₗ[ℂ]
      cuspPrincipalWindowSpace N hN basis e a b :=
  (cuspParityOperator N hN σ).restrict
    (fun x hx => cuspParityOperator_preserves_window N hN basis e henergy hgraph a b σ x hx)

theorem cuspWindowParity_idempotent {κ : Type*} (N : ℕ) [NeZero N] (hN : 0<N)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (henergy : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (basis j:AutomorphicSpace N) ((e j:ℂ) • (basis j:AutomorphicSpace N)))
    (a b σ : ℝ) (hσ : σ^2=1) :
    IsIdempotentElem (cuspWindowParity N hN basis e henergy hgraph a b σ) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  exact parityProjection_idempotent N σ hσ (x.val:AutomorphicSpace N)

#print axioms wave_commuting_preserves_cuspPrincipalWindowSpace
#print axioms cuspParityOperator_preserves_window
#print axioms cuspWindowParity_idempotent

end QuantitativeMaass
