module

public import QuantitativeMaassFriedrichsGraphV1
public import Mathlib.Analysis.InnerProductSpace.LinearPMap

set_option autoImplicit false
@[expose] public noncomputable section

open Set
open scoped Topology InnerProductSpace

namespace QuantitativeMaass

/-- The actual energy-resolvent graph as a linear subspace. -/
def friedrichsGraphSubmodule (N : ℕ) :
    Submodule ℂ (AutomorphicSpace N × AutomorphicSpace N) where
  carrier := {p | FriedrichsGraph N p.1 p.2}
  zero_mem' := by simp [FriedrichsGraph]
  add_mem' := by
    intro p q hp hq
    change friedrichsResolvent N ((p.1+q.1)+(p.2+q.2))=p.1+q.1
    rw [add_add_add_comm,map_add,hp,hq]
  smul_mem' := by
    intro c p hp
    change friedrichsResolvent N (c • p.1+c • p.2)=c • p.1
    rw [← smul_add,map_smul,hp]

/-- A densely defined operator on the literal quotient Hilbert space, obtained
from its proved single-valued energy-resolvent graph. -/
def friedrichsLaplacian (N : ℕ) : AutomorphicSpace N →ₗ.[ℂ] AutomorphicSpace N :=
  (friedrichsGraphSubmodule N).toLinearPMap

theorem friedrichsLaplacian_graph (N : ℕ) :
    (friedrichsLaplacian N).graph=friedrichsGraphSubmodule N := by
  apply Submodule.toLinearPMap_graph_eq
  intro p hp hz
  change FriedrichsGraph N p.1 p.2 at hp
  have hp' : FriedrichsGraph N 0 p.2 := by simpa only [hz] using hp
  exact friedrichsGraph_singleValued N hp' (by simp [FriedrichsGraph])

theorem friedrichsLaplacian_mem_graph (N : ℕ) (x y : AutomorphicSpace N) :
    (x,y) ∈ (friedrichsLaplacian N).graph ↔ FriedrichsGraph N x y := by
  rw [friedrichsLaplacian_graph]
  rfl

theorem friedrichsLaplacian_denseDomain (N : ℕ) :
    Dense ((friedrichsLaplacian N).domain : Set (AutomorphicSpace N)) := by
  apply (friedrichsGraph_denseDomain N).mono
  rintro x ⟨y,hy⟩
  change x ∈ (friedrichsGraphSubmodule N).map (LinearMap.fst ℂ _ _)
  exact ⟨(x,y),hy,rfl⟩

theorem friedrichsGraphSubmodule_adjoint (N : ℕ) :
    (friedrichsGraphSubmodule N).adjoint=friedrichsGraphSubmodule N := by
  ext p
  rw [Submodule.mem_adjoint_iff]
  change (∀ a b, FriedrichsGraph N a b → inner ℂ b p.1-inner ℂ a p.2=0) ↔
    FriedrichsGraph N p.1 p.2
  simp only [sub_eq_zero]
  exact (friedrichsGraph_iff_adjoint N p.1 p.2).symm

/-- The constructed quotient realization is self-adjoint in Mathlib's actual
unbounded-operator API. No self-adjointness or form-core hypothesis is assumed. -/
theorem friedrichsLaplacian_isSelfAdjoint (N : ℕ) :
    IsSelfAdjoint (friedrichsLaplacian N) := by
  apply LinearPMap.isSelfAdjoint_def.mpr
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (friedrichsLaplacian_denseDomain N),
    friedrichsLaplacian_graph,friedrichsGraphSubmodule_adjoint]

theorem friedrichsLaplacian_closed (N : ℕ) : (friedrichsLaplacian N).IsClosed :=
  (friedrichsLaplacian_isSelfAdjoint N).isClosed

theorem friedrichsLaplacian_nonnegative (N : ℕ)
    (x : (friedrichsLaplacian N).domain) :
    0≤(inner ℂ x.val (friedrichsLaplacian N x)).re := by
  apply friedrichsGraph_nonnegative N
  apply (friedrichsLaplacian_mem_graph N _ _).mp
  exact (LinearPMap.mem_graph_iff _).mpr ⟨x,rfl,rfl⟩

/-- Exact differential agreement, expressed without any arbitrary domain
identification: every smooth compact Poincaré vector and its literal
Laplacian belong to the constructed operator graph. -/
theorem friedrichsLaplacian_poincareSeed (N : ℕ) (u : SmoothUpperSeed) :
    (poincareSeedVector N u,poincareSeedVector N u.laplacian) ∈
      (friedrichsLaplacian N).graph :=
  (friedrichsLaplacian_mem_graph N _ _).mpr (friedrichsGraph_poincareSeed N u)

#print axioms friedrichsLaplacian_isSelfAdjoint
#print axioms friedrichsLaplacian_nonnegative
#print axioms friedrichsLaplacian_poincareSeed

end QuantitativeMaass
