module

public import QuantitativeMaassBasisProjectionTailV1
public import QuantitativeMaassCutoffWideLeakageV1
public import QuantitativeMaassLVCuspidalProjectionV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set

namespace QuantitativeMaass.Weighted

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) :=
  inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) :=
  inferInstance

/-- Multiplication followed by the actual cuspidal projection. This
definition keeps the projection which multiplication need not preserve. -/
def cuspidalCutoff (N : ℕ) (hN : 0<N) (b : Cutoff N) :
    AutomorphicSpace N →L[ℂ] localCuspidalSpace N hN :=
  (localCuspidalSpace N hN).orthogonalProjectionOnto.comp
    (quotientLocalization N b.value b.smooth)

theorem cuspidalCutoff_inner (N : ℕ) (hN : 0<N) (b : Cutoff N)
    (f : localCuspidalSpace N hN) (g : AutomorphicSpace N) :
    inner ℂ f (cuspidalCutoff N hN b g)=
      inner ℂ (f.val.val) (multiplier N b g.val) := by
  change inner ℂ f ((localCuspidalSpace N hN).orthogonalProjectionOnto
    (quotientLocalization N b.value b.smooth g))=_
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  have he := congrArg (fun A => A g)
    (quotientLocalization_ambient N b.value b.smooth b.invariant
      b.bound_nonneg b.value_bound b.gradient_bound)
  change (quotientLocalization N b.value b.smooth g).val=multiplier N b g.val at he
  change inner ℂ f.val.val (quotientLocalization N b.value b.smooth g).val=_
  rw [he]

theorem outside_principal_window_distance {ι : Type*} (e : ι → ℝ)
    (t L : ℝ) (ht : L+3≤t) (i : ι)
    (hi : i∉principalWindowIndices e (t-(L+3)) (t+(L+3))) :
    L+3≤|Real.sqrt (e i-1/4)-t| := by
  by_cases he : 1/4≤e i
  · have hnot : ¬(t-(L+3)≤Real.sqrt (e i-1/4) ∧
        Real.sqrt (e i-1/4)≤t+(L+3)) := fun h => hi ⟨he,h⟩
    by_cases hleft : t-(L+3)≤Real.sqrt (e i-1/4)
    · have hright : t+(L+3)<Real.sqrt (e i-1/4) := lt_of_not_ge (fun h => hnot ⟨hleft,h⟩)
      have hh := le_abs_self (Real.sqrt (e i-1/4)-t)
      linarith
    · have hh := neg_le_abs (Real.sqrt (e i-1/4)-t)
      have hl := lt_of_not_ge hleft
      linarith
  · rw [Real.sqrt_eq_zero_of_nonpos (by linarith),zero_sub,abs_neg]
    exact ht.trans (le_abs_self t)

/-- The cuspidal part of a smooth cutoff applied to a unit eigenband has
squared norm outside the larger band at most its dimension times L⁻².
Both orthogonal projections are the actual geometric projections. -/
theorem cuspidalCutoff_wide_tail {ι κ : Type*} [Fintype κ]
    (N : ℕ) (hN : 0<N) (b : Cutoff N)
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
    ∑ j,‖cuspidalCutoff N hN b (g j)-W.starProjection (cuspidalCutoff N hN b (g j))‖^2≤
      16*b.gradientBound^2*(Fintype.card κ:ℝ)/L^2 := by
  classical
  dsimp only
  let S := principalWindowIndices e (t-(L+3)) (t+(L+3))
  let W := cuspPrincipalWindowSpace N hN basis e (t-(L+3)) (t+(L+3))
  let : FiniteDimensional ℂ W := cuspPrincipalWindowSpace_finiteDimensional
    N hN basis e he hgraph (t-(L+3)) (t+(L+3))
  have htail (j : κ) :
      ‖cuspidalCutoff N hN b (g j)-W.starProjection (cuspidalCutoff N hN b (g j))‖^2=
        ∑' i : {i // i∉S},‖inner ℂ (basis i.val).val.val (multiplier N b (g j).val)‖^2 := by
    rw [hilbertBasis_projection_tail basis S]
    exact tsum_congr (fun i => by rw [cuspidalCutoff_inner])
  change (∑ j,‖cuspidalCutoff N hN b (g j)-W.starProjection (cuspidalCutoff N hN b (g j))‖^2)≤_
  simp_rw [htail]
  have ho := basis.orthonormal.comp_linearIsometry (localCuspidalSpace N hN).subtypeₗᵢ
  exact smooth_cutoff_outside_wide_band N b (fun i : {i // i∉S} => e i.val) μ
    (fun i : {i // i∉S} => (basis i.val:AutomorphicSpace N)) g
    (ho.comp Subtype.val Subtype.val_injective) hg
    (fun i => he i.val) hμ (fun i => hgraph i.val) hggraph t L hL hin
    (fun i => outside_principal_window_distance e t L ht i.val i.property)

#print axioms cuspidalCutoff_inner
#print axioms outside_principal_window_distance
#print axioms cuspidalCutoff_wide_tail

end QuantitativeMaass.Weighted
