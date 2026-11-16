module

public import QuantitativeMaassSharpCountExistenceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology InnerProductSpace

namespace QuantitativeMaass

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance

/-- A vector whose Hilbert coefficients vanish off a finite set lies in the
algebraic span of exactly those basis vectors. -/
theorem hilbertBasis_mem_finite_span {ι H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (b : HilbertBasis ι ℂ H)
    (S : Set ι) (hS : S.Finite) (x : H) (hx : ∀ i,i∉S → b.repr x i=0) :
    x∈Submodule.span ℂ (Set.range (fun i : S => b i.val)) := by
  classical
  have hz : HasSum (fun i => b.repr x i • b i)
      (∑ i∈hS.toFinset,b.repr x i • b i) := by
    apply hasSum_sum_of_ne_finset_zero
    intro i hi
    rw [hx i (by simpa only [Set.Finite.mem_toFinset] using hi),zero_smul]
  rw [(b.hasSum_repr x).unique hz]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨⟨i,hS.mem_toFinset.mp hi⟩,rfl⟩

/-- The actual finite principal band inside the geometric cusp Hilbert space. -/
abbrev cuspPrincipalWindowSpace {κ : Type*} (N : ℕ) (hN : 0<N)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ) (a b : ℝ) :
    Submodule ℂ (localCuspidalSpace N hN) :=
  Submodule.span ℂ (Set.range (fun i : principalWindowIndices e a b => basis i.val))

theorem cuspPrincipalWindowSpace_finiteDimensional {κ : Type*} (N : ℕ) (hN : 0<N)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (henergy : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (basis j:AutomorphicSpace N) ((e j:ℂ) • (basis j:AutomorphicSpace N)))
    (a b : ℝ) : FiniteDimensional ℂ (cuspPrincipalWindowSpace N hN basis e a b) := by
  have ho : Orthonormal ℂ (fun j => (basis j:AutomorphicSpace N)) :=
    basis.orthonormal.comp_linearIsometry (localCuspidalSpace N hN).subtypeₗᵢ
  let : Fintype (principalWindowIndices e a b) :=
    (principalWindowIndices_finite N hN _ ho (fun j => (basis j).property) e henergy hgraph a b).fintype
  exact FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

theorem cuspPrincipalWindowSpace_finrank {κ : Type*} (N : ℕ) (hN : 0<N)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (henergy : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (basis j:AutomorphicSpace N) ((e j:ℂ) • (basis j:AutomorphicSpace N)))
    (a b : ℝ) : Module.finrank ℂ (cuspPrincipalWindowSpace N hN basis e a b)=
      Nat.card (principalWindowIndices e a b) := by
  have ho : Orthonormal ℂ (fun j => (basis j:AutomorphicSpace N)) :=
    basis.orthonormal.comp_linearIsometry (localCuspidalSpace N hN).subtypeₗᵢ
  let : Fintype (principalWindowIndices e a b) :=
    (principalWindowIndices_finite N hN _ ho (fun j => (basis j).property) e henergy hgraph a b).fintype
  rw [Nat.card_eq_fintype_card]
  exact finrank_span_eq_card (basis.orthonormal.linearIndependent.comp _ Subtype.val_injective)

#print axioms hilbertBasis_mem_finite_span
#print axioms cuspPrincipalWindowSpace_finiteDimensional
#print axioms cuspPrincipalWindowSpace_finrank

end QuantitativeMaass
