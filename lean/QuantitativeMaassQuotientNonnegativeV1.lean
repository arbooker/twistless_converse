module

public import QuantitativeMaassPoincareGraphLinearV1
public import QuantitativeMaassPoincareEnergyIdentityV1
public import QuantitativeMaassQuotientLaplacianV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set
open scoped Topology InnerProductSpace

namespace QuantitativeMaass

theorem poincareGraph_nonnegative (N : ℕ) {x y : AutomorphicSpace N}
    (h : PoincareGraph N x y) : 0≤(inner ℂ x y).re := by
  obtain ⟨u,rfl,rfl⟩ := h
  exact poincareSeedVector_laplacian_nonneg N u

/-- Nonnegativity passes to the actual graph closure by continuity of
the Hilbert inner product in both coordinates. -/
theorem poincareClosedGraph_nonnegative (N : ℕ)
    {p : AutomorphicSpace N × AutomorphicSpace N} (hp : p∈poincareClosedGraph N) :
    0≤(inner ℂ p.1 p.2).re := by
  have hs : IsClosed {p : AutomorphicSpace N × AutomorphicSpace N |
      0≤(inner ℂ p.1 p.2).re} :=
    isClosed_le continuous_const (Complex.continuous_re.comp (continuous_fst.inner continuous_snd))
  apply closure_minimal _ hs hp
  intro p hp
  exact poincareGraph_nonnegative N ((poincareLinearGraph_mem_iff N p).mp hp)

/-- The constructed densely defined closed symmetric quotient operator
is nonnegative. This is proved from the literal global Green energy and
is not an assumption about its spectrum. -/
theorem quotientLaplacian_nonnegative (N : ℕ) (x : quotientLaplacianDomain N) :
    0≤(inner ℂ x.val (quotientLaplacian N x)).re :=
  poincareClosedGraph_nonnegative N (quotientLaplacian_graph N x)

#print axioms quotientLaplacian_nonnegative

end QuantitativeMaass
