module

public import QuantitativeMaassPoincareClosedGraphV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set
open scoped Topology InnerProductSpace

namespace QuantitativeMaass

/-- The domain obtained from the product-Hilbert closure of the literal
smooth Poincaré differential graph. -/
def quotientLaplacianDomain (N : ℕ) : Submodule ℂ (AutomorphicSpace N) :=
  (poincareClosedGraph N).map (LinearMap.fst ℂ (AutomorphicSpace N) (AutomorphicSpace N))

theorem quotientLaplacianDomain_exists (N : ℕ) (x : quotientLaplacianDomain N) :
    ∃ y, (x.val,y)∈poincareClosedGraph N := by
  obtain ⟨p,hp,he⟩ := x.property
  change p.1=x.val at he
  refine ⟨p.2,?_⟩
  rw [← he]
  exact hp

/-- A genuine densely defined closed symmetric quotient Laplacian,
constructed from the literal smooth Poincaré expression. No boundedness or
self-adjointness claim is included in this definition. -/
def quotientLaplacian (N : ℕ) : quotientLaplacianDomain N →ₗ[ℂ] AutomorphicSpace N where
  toFun x := (quotientLaplacianDomain_exists N x).choose
  map_add' x y := by
    apply poincareClosedGraph_singleValued N
      ((quotientLaplacianDomain_exists N (x+y)).choose_spec)
    exact (poincareClosedGraph N).add_mem
      ((quotientLaplacianDomain_exists N x).choose_spec)
      ((quotientLaplacianDomain_exists N y).choose_spec)
  map_smul' c x := by
    apply poincareClosedGraph_singleValued N
      ((quotientLaplacianDomain_exists N (c•x)).choose_spec)
    exact (poincareClosedGraph N).smul_mem c
      ((quotientLaplacianDomain_exists N x).choose_spec)

theorem quotientLaplacian_graph (N : ℕ) (x : quotientLaplacianDomain N) :
    (x.val,quotientLaplacian N x)∈poincareClosedGraph N :=
  (quotientLaplacianDomain_exists N x).choose_spec

theorem quotientLaplacian_graph_iff (N : ℕ) (x y : AutomorphicSpace N) :
    (x,y)∈poincareClosedGraph N ↔
      ∃ hx : x∈quotientLaplacianDomain N, quotientLaplacian N ⟨x,hx⟩=y := by
  constructor
  · intro h
    have hx : x∈quotientLaplacianDomain N := ⟨(x,y),h,rfl⟩
    exact ⟨hx,poincareClosedGraph_singleValued N (quotientLaplacian_graph N ⟨x,hx⟩) h⟩
  · rintro ⟨hx,rfl⟩
    exact quotientLaplacian_graph N ⟨x,hx⟩

theorem quotientLaplacian_denseDomain (N : ℕ) :
    Dense (quotientLaplacianDomain N : Set (AutomorphicSpace N)) := by
  apply (poincareClosedGraph_denseDomain N).mono
  rintro x ⟨y,h⟩
  exact ⟨(x,y),h,rfl⟩

theorem quotientLaplacian_symmetric (N : ℕ) (x y : quotientLaplacianDomain N) :
    inner ℂ (quotientLaplacian N x) y.val=inner ℂ x.val (quotientLaplacian N y) :=
  poincareClosedGraph_symmetric N (quotientLaplacian_graph N x) (quotientLaplacian_graph N y)

theorem quotientLaplacian_closed (N : ℕ) :
    IsClosed {p : AutomorphicSpace N × AutomorphicSpace N |
      ∃ h : p.1∈quotientLaplacianDomain N, quotientLaplacian N ⟨p.1,h⟩=p.2} := by
  convert poincareClosedGraph_closed N using 1
  ext p
  exact (quotientLaplacian_graph_iff N p.1 p.2).symm

theorem poincareSeedVector_mem_quotientLaplacianDomain (N : ℕ) (u : SmoothUpperSeed) :
    poincareSeedVector N u∈quotientLaplacianDomain N :=
  ⟨_,poincareClosedGraph_contains N u,rfl⟩

/-- Exact agreement with the actual Laplace differential expression on all
smooth compact Poincaré seeds. -/
theorem quotientLaplacian_poincareSeed (N : ℕ) (u : SmoothUpperSeed) :
    quotientLaplacian N ⟨poincareSeedVector N u,
      poincareSeedVector_mem_quotientLaplacianDomain N u⟩=
        poincareSeedVector N u.laplacian :=
  poincareClosedGraph_singleValued N (quotientLaplacian_graph N _)
    (poincareClosedGraph_contains N u)

#print axioms quotientLaplacian
#print axioms quotientLaplacian_denseDomain
#print axioms quotientLaplacian_closed
#print axioms quotientLaplacian_poincareSeed

end QuantitativeMaass
