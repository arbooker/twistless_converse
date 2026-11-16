module

public import QuantitativeMaassBasisProjectionTailV1
public import QuantitativeMaassQuotientWeightWideLeakageV1
public import QuantitativeMaassQuotientWeightAutomorphicV1
public import QuantitativeMaassCuspidalCutoffTailV1
public import QuantitativeMaassLVCuspidalProjectionV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set

namespace QuantitativeMaass

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) :=
  inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) :=
  inferInstance

/-- Multiplication followed by the actual cuspidal projection. This
definition keeps the projection which multiplication need not preserve. -/
def cuspidalQuotientWeight (N : ℕ) (hN : 0<N) {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1≤v) :
    AutomorphicSpace N →L[ℂ] localCuspidalSpace N hN :=
  (localCuspidalSpace N hN).orthogonalProjectionOnto.comp
    (quotientWeightAutomorphicMultiplier N hε hv)

theorem cuspidalQuotientWeight_inner (N : ℕ) (hN : 0<N) {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1≤v)
    (f : localCuspidalSpace N hN) (g : AutomorphicSpace N) :
    inner ℂ f (cuspidalQuotientWeight N hN hε hv g)=
      inner ℂ (f.val.val) (quotientWeightMultiplier N hε hv g.val) := by
  change inner ℂ f ((localCuspidalSpace N hN).orthogonalProjectionOnto
    (quotientWeightAutomorphicMultiplier N hε hv g))=_
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  change inner ℂ f.val.val (quotientWeightAutomorphicMultiplier N hε hv g).val=_
  rw [quotientWeightAutomorphicMultiplier_value]

/-- The cuspidal part of the literal orbit weight applied to a unit eigenband has
squared norm outside the larger band at most its dimension times L⁻².
Both orthogonal projections are the actual geometric projections. -/
theorem cuspidalQuotientWeight_wide_tail {ι κ : Type*} [Fintype κ]
    (N : ℕ) (hN : 0<N) {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1≤v)
    (basis : HilbertBasis ι ℂ (localCuspidalSpace N hN)) (e : ι → ℝ)
    (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (basis i:AutomorphicSpace N)
      ((e i:ℂ) • (basis i:AutomorphicSpace N)))
    (g : κ → AutomorphicSpace N) (μ : κ → ℝ)
    (hg : Orthonormal ℂ g) (hμ : ∀ j,0≤μ j)
    (hggraph : ∀ j,FriedrichsGraph N (g j) ((μ j:ℂ) • g j))
    (t L : ℝ) (hL : 0<L) (ht : L+3≤t)
    (hin : ∀ j,|Real.sqrt (μ j-1/4)-t|≤1) :
    let W := cuspPrincipalWindowSpace N hN basis e (t-(L+3)) (t+(L+3))
    let : FiniteDimensional ℂ W := cuspPrincipalWindowSpace_finiteDimensional
      N hN basis e he hgraph (t-(L+3)) (t+(L+3))
    ∑ j,‖cuspidalQuotientWeight N hN hε hv (g j)-W.starProjection (cuspidalQuotientWeight N hN hε hv (g j))‖^2≤
      16*(4*quotientWeightBound ε*(2*v:ℝ))^2*(Fintype.card κ:ℝ)/L^2 := by
  classical
  dsimp only
  let S := principalWindowIndices e (t-(L+3)) (t+(L+3))
  let W := cuspPrincipalWindowSpace N hN basis e (t-(L+3)) (t+(L+3))
  let : FiniteDimensional ℂ W := cuspPrincipalWindowSpace_finiteDimensional
    N hN basis e he hgraph (t-(L+3)) (t+(L+3))
  have htail (j : κ) :
      ‖cuspidalQuotientWeight N hN hε hv (g j)-W.starProjection (cuspidalQuotientWeight N hN hε hv (g j))‖^2=
        ∑' i : {i // i∉S},‖inner ℂ (basis i.val).val.val (quotientWeightMultiplier N hε hv (g j).val)‖^2 := by
    rw [hilbertBasis_projection_tail basis S]
    exact tsum_congr (fun i => by rw [cuspidalQuotientWeight_inner])
  change (∑ j,‖cuspidalQuotientWeight N hN hε hv (g j)-W.starProjection (cuspidalQuotientWeight N hN hε hv (g j))‖^2)≤_
  simp_rw [htail]
  have ho := basis.orthonormal.comp_linearIsometry (localCuspidalSpace N hN).subtypeₗᵢ
  exact quotientWeight_outside_wide_band N hε hv (fun i : {i // i∉S} => e i.val) μ
    (fun i : {i // i∉S} => (basis i.val:AutomorphicSpace N)) g
    (ho.comp Subtype.val Subtype.val_injective) hg
    (fun i => he i.val) hμ (fun i => hgraph i.val) hggraph t L hL hin
    (fun i => Weighted.outside_principal_window_distance e t L ht i.val i.property)

#print axioms cuspidalQuotientWeight_inner
#print axioms cuspidalQuotientWeight_wide_tail

end QuantitativeMaass
