module

public import QuantitativeMaassPoincareGraphV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set Topology
open scoped Topology InnerProductSpace

namespace QuantitativeMaass

/-- Finite linear combinations of actual smooth Poincaré graph pairs. -/
def poincareLinearGraph (N : ℕ) : Submodule ℂ (AutomorphicSpace N × AutomorphicSpace N) :=
  Submodule.span ℂ {p | PoincareGraph N p.1 p.2}

/-- Graph closure in the product of the actual quotient Hilbert spaces.
This is not asserted to equal its adjoint graph. -/
def poincareClosedGraph (N : ℕ) : Submodule ℂ (AutomorphicSpace N × AutomorphicSpace N) :=
  (poincareLinearGraph N).topologicalClosure

theorem poincareLinearGraph_symmetric (N : ℕ)
    {p q : AutomorphicSpace N × AutomorphicSpace N}
    (hp : p∈poincareLinearGraph N) (hq : q∈poincareLinearGraph N) :
    inner ℂ p.2 q.1=inner ℂ p.1 q.2 := by
  apply Submodule.span_induction₂ (p := fun p q _ _ => inner ℂ p.2 q.1=inner ℂ p.1 q.2)
    _ _ _ _ _ _ _ hp hq
  · intro p q hp hq
    exact poincareGraph_symmetric N hp hq
  · intro q _; simp
  · intro p _; simp
  · intro p q r _ _ _ hp hq
    simp only [Prod.fst_add,Prod.snd_add,inner_add_left,hp,hq]
  · intro p q r _ _ _ hq hr
    simp only [Prod.fst_add,Prod.snd_add,inner_add_right,hq,hr]
  · intro c p q _ _ h
    change inner ℂ (c • p.2) q.1=inner ℂ (c • p.1) q.2
    exact (inner_smul_left p.2 q.1 c).trans ((congrArg (fun z : ℂ => star c*z) h).trans (inner_smul_left p.1 q.2 c).symm)
  · intro c p q _ _ h
    change inner ℂ p.2 (c • q.1)=inner ℂ p.1 (c • q.2)
    exact (inner_smul_right p.2 q.1 c).trans ((congrArg (fun z : ℂ => c*z) h).trans (inner_smul_right p.1 q.2 c).symm)

theorem poincareClosedGraph_symmetric (N : ℕ)
    {p q : AutomorphicSpace N × AutomorphicSpace N}
    (hp : p∈poincareClosedGraph N) (hq : q∈poincareClosedGraph N) :
    inner ℂ p.2 q.1=inner ℂ p.1 q.2 := by
  have hfirst (q : AutomorphicSpace N × AutomorphicSpace N)
      (hq : q∈poincareLinearGraph N) :
      ∀ p∈poincareClosedGraph N, inner ℂ p.2 q.1=inner ℂ p.1 q.2 := by
    apply closure_minimal
    · intro p hp
      exact poincareLinearGraph_symmetric N hp hq
    · exact isClosed_eq (continuous_snd.inner continuous_const)
        (continuous_fst.inner continuous_const)
  have hs : IsClosed {q : AutomorphicSpace N × AutomorphicSpace N |
      inner ℂ p.2 q.1=inner ℂ p.1 q.2} :=
    isClosed_eq (continuous_const.inner continuous_fst)
      (continuous_const.inner continuous_snd)
  exact closure_minimal (fun q hq => hfirst q hq p hp) hs hq

theorem poincareClosedGraph_contains (N : ℕ) (u : SmoothUpperSeed) :
    (poincareSeedVector N u,poincareSeedVector N u.laplacian)∈poincareClosedGraph N :=
  (poincareLinearGraph N).le_topologicalClosure (Submodule.subset_span ⟨u,rfl,rfl⟩)

theorem poincareClosedGraph_singleValued (N : ℕ) {x y z : AutomorphicSpace N}
    (hy : (x,y)∈poincareClosedGraph N) (hz : (x,z)∈poincareClosedGraph N) : y=z := by
  apply (poincareSeedVector_dense N).eq_of_inner_left (𝕜 := ℂ)
  intro u
  exact (poincareClosedGraph_symmetric N hy (poincareClosedGraph_contains N u)).trans
    (poincareClosedGraph_symmetric N hz (poincareClosedGraph_contains N u)).symm

theorem poincareClosedGraph_denseDomain (N : ℕ) :
    Dense {x : AutomorphicSpace N | ∃ y, (x,y)∈poincareClosedGraph N} := by
  apply (poincareSeedVector_dense N).mono
  rintro x ⟨u,rfl⟩
  exact ⟨_,poincareClosedGraph_contains N u⟩

theorem poincareClosedGraph_closed (N : ℕ) :
    IsClosed (poincareClosedGraph N : Set (AutomorphicSpace N × AutomorphicSpace N)) :=
  (poincareLinearGraph N).isClosed_topologicalClosure

#print axioms poincareClosedGraph_symmetric
#print axioms poincareClosedGraph_singleValued
#print axioms poincareClosedGraph_denseDomain

end QuantitativeMaass
