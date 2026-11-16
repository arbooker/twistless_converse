module

public import QuantitativeMaassSpectralWindowInvariantV1
public import QuantitativeMaassFiniteProjectionTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open AsymptoticCongruenceStrip
open scoped Topology InnerProductSpace

namespace QuantitativeMaass

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance

/-- The original cusp energy vectors in the interval form an orthonormal
basis of their actual finite spectral band. -/
def cuspPrincipalWindowBasis {κ : Type*} (N : ℕ) (hN : 0<N)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ) (a b : ℝ)
    [Fintype (principalWindowIndices e a b)] :
    OrthonormalBasis (principalWindowIndices e a b) ℂ (cuspPrincipalWindowSpace N hN basis e a b) := by
  let ho := basis.orthonormal.comp (fun i : principalWindowIndices e a b => i.val) Subtype.val_injective
  exact (Module.Basis.span ho.linearIndependent).toOrthonormalBasis
    (by
      convert! orthonormal_span ho
      simp [Module.Basis.span_apply])

theorem cuspPrincipalWindowBasis_coe {κ : Type*} (N : ℕ) (hN : 0<N)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ) (a b : ℝ)
    [Fintype (principalWindowIndices e a b)] (i : principalWindowIndices e a b) :
    ((cuspPrincipalWindowBasis N hN basis e a b i : localCuspidalSpace N hN):AutomorphicSpace N)=
      (basis i.val:AutomorphicSpace N) := by
  let ho := basis.orthonormal.comp (fun i : principalWindowIndices e a b => i.val) Subtype.val_injective
  have hon : Orthonormal ℂ (Module.Basis.span ho.linearIndependent) := by
    convert! orthonormal_span ho
    simp [Module.Basis.span_apply]
  have hb : cuspPrincipalWindowBasis N hN basis e a b i=Module.Basis.span ho.linearIndependent i :=
    congrFun (Module.Basis.coe_toOrthonormalBasis (Module.Basis.span ho.linearIndependent) hon) i
  rw [hb,Module.Basis.span_apply]
  rfl


theorem cuspWindowParity_symmetric {κ : Type*} (N : ℕ) [NeZero N] (hN : 0<N)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (henergy : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (basis j:AutomorphicSpace N) ((e j:ℂ) • (basis j:AutomorphicSpace N)))
    (a b σ : ℝ) : (cuspWindowParity N hN basis e henergy hgraph a b σ).IsSymmetric := by
  intro x y
  change inner ℂ (parityProjection N σ (x.val:AutomorphicSpace N)) (y.val:AutomorphicSpace N)=
    inner ℂ (x.val:AutomorphicSpace N) (parityProjection N σ (y.val:AutomorphicSpace N))
  exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (parityProjection_selfAdjoint N σ) _ _

/-- Exact identification of the parity-weighted sharp sum with the dimension
of the range of the actual parity projection on the finite spectral band. -/
theorem sharp_parity_weight_eq_dimension {κ : Type*} (N : ℕ) [NeZero N] (hN : 0<N)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (henergy : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (basis j:AutomorphicSpace N) ((e j:ℂ) • (basis j:AutomorphicSpace N)))
    (a b σ : ℝ) (hσ : σ^2=1) :
    principalWindowWeight e (fun j => ‖parityProjection N σ (basis j:AutomorphicSpace N)‖^2) a b=
      (Module.finrank ℂ (LinearMap.range (cuspWindowParity N hN basis e henergy hgraph a b σ)):ℝ) := by
  have ho : Orthonormal ℂ (fun j => (basis j:AutomorphicSpace N)) :=
    basis.orthonormal.comp_linearIsometry (localCuspidalSpace N hN).subtypeₗᵢ
  let : Fintype (principalWindowIndices e a b) :=
    (principalWindowIndices_finite N hN _ ho (fun j => (basis j).property) e henergy hgraph a b).fintype
  let : FiniteDimensional ℂ (cuspPrincipalWindowSpace N hN basis e a b) :=
    cuspPrincipalWindowSpace_finiteDimensional N hN basis e henergy hgraph a b
  have hh := finite_projection_energy_eq_finrank (cuspPrincipalWindowBasis N hN basis e a b)
    (cuspWindowParity N hN basis e henergy hgraph a b σ)
    (cuspWindowParity_idempotent N hN basis e henergy hgraph a b σ hσ)
    (cuspWindowParity_symmetric N hN basis e henergy hgraph a b σ)
  unfold principalWindowWeight
  rw [tsum_fintype]
  rw [← hh]
  apply Finset.sum_congr rfl
  intro i _
  change ‖parityProjection N σ (basis i.val:AutomorphicSpace N)‖^2=
    ‖parityProjection N σ ((cuspPrincipalWindowBasis N hN basis e a b i : localCuspidalSpace N hN):AutomorphicSpace N)‖^2
  rw [cuspPrincipalWindowBasis_coe]

/-- The actual sharp LV lower sum is bounded by the genuine finite parity
spectral dimension, without choosing a simultaneous parity eigenbasis. -/
theorem sharp_parity_LV_weight_le_dimension {κ : Type*}
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (A B : ℤ) (hAB : (p:ℤ)*A+(N:ℤ)*B=1) (d : ℕ)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (henergy : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (basis j:AutomorphicSpace N) ((e j:ℂ) • (basis j:AutomorphicSpace N)))
    (a b σ : ℝ) (hσ : σ^2=1) :
    principalWindowWeight e (fun j =>
      (inner ℂ (actualLVFilter N p hN hpN A B hAB d (parityProjection N σ (basis j:AutomorphicSpace N)))
        (parityProjection N σ (basis j:AutomorphicSpace N))).re) a b≤
      (Module.finrank ℂ (LinearMap.range (cuspWindowParity N hN basis e henergy hgraph a b σ)):ℝ) := by
  have ho : Orthonormal ℂ (fun j => (basis j:AutomorphicSpace N)) :=
    basis.orthonormal.comp_linearIsometry (localCuspidalSpace N hN).subtypeₗᵢ
  let : Fintype (principalWindowIndices e a b) :=
    (principalWindowIndices_finite N hN _ ho (fun j => (basis j).property) e henergy hgraph a b).fintype
  rw [← sharp_parity_weight_eq_dimension N hN basis e henergy hgraph a b σ hσ]
  apply Summable.tsum_le_tsum _ Summable.of_finite Summable.of_finite
  intro i
  have hb := (actualLVFilter_quadratic_bounds N p hN hpN hNp hpres A B hAB d
    (parityProjection N σ (basis i.val:AutomorphicSpace N))).2
  have hc : localCuspidalProjection N hN (parityProjection N σ (basis i.val:AutomorphicSpace N))=
      parityProjection N σ (basis i.val:AutomorphicSpace N) :=
    Submodule.starProjection_eq_self_iff.mpr
      (parityProjection_mem_localCuspidalSpace N hN σ _ (basis i.val).property)
  simpa only [hc] using hb

#print axioms cuspPrincipalWindowBasis_coe
#print axioms cuspWindowParity_symmetric
#print axioms sharp_parity_weight_eq_dimension
#print axioms sharp_parity_LV_weight_le_dimension

end QuantitativeMaass
