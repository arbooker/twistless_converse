module

public import QuantitativeMaassShortIntervalWeylV1
public import QuantitativeMaassParityWindowLowerV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology InnerProductSpace

namespace QuantitativeMaass

/-- The short-interval Weyl law in each genuine reflection eigenspace. The
opposite parity lower bound and exact dimension splitting supply the sharp upper bound. -/
theorem cuspParityWindow_short_interval_weyl {κ : Type*} (N : ℕ) [NeZero N] (hN : 0<N)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (henergy : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (basis j:AutomorphicSpace N) ((e j:ℂ) • (basis j:AutomorphicSpace N)))
    (σ : ℝ) (hσ : σ^2=1) (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t =>
      (Module.finrank ℂ (LinearMap.range (cuspWindowParity N hN basis e henergy hgraph t (t+ε t) σ)):ℝ)/(t*ε t))
      atTop (𝓝 ((quotientMeasure N).real univ/(4*Real.pi))) := by
  have ho : Orthonormal ℂ (fun j => (basis j:AutomorphicSpace N)) :=
    basis.orthonormal.comp_linearIsometry (localCuspidalSpace N hN).subtypeₗᵢ
  let V := (quotientMeasure N).real univ/(4*Real.pi)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hh := cuspParityWindow_dimension_eventual_lower N hN basis e henergy hgraph σ hσ ε hε hproduct
      (V-a) (sub_pos.mpr ha)
    simpa only [V,sub_sub_cancel] using hh
  · intro b hb
    have hgap : 0<(b-V)/2 := by dsimp [V]; linarith
    have hu := principal_sharp_count_eventual_upper N hN _ ho (fun j => (basis j).property)
      e henergy hgraph ε hε hproduct ((b-V)/2) hgap
    have hl := cuspParityWindow_dimension_eventual_lower N hN basis e henergy hgraph (-σ)
      (by simpa only [neg_sq] using hσ) ε hε hproduct ((b-V)/2) hgap
    filter_upwards [hu,hl] with t hut hlt
    have hadd := congrArg (fun n : ℕ => (n:ℝ))
      (cuspWindowParity_dimensions_add N hN basis e henergy hgraph t (t+ε t) σ hσ)
    rw [Nat.cast_add] at hadd
    have hd := congrArg (fun x : ℝ => x/(t*ε t)) hadd
    rw [add_div] at hd
    have hV : (quotientMeasure N).real univ/(2*Real.pi)=2*V := by dsimp [V]; ring
    rw [hV] at hut
    change V-(b-V)/2<_ at hlt
    linarith

/-- The canonical actual cusp energy basis obeys both parity Weyl laws at every
positive level; reflection eigenspaces are defined inside its finite spectral bands. -/
theorem exists_cusp_spectrum_parity_short_weyl (N : ℕ) (hN : 0<N) :
    letI : NeZero N := ⟨hN.ne'⟩
    ∃ (κ : Type) (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
      (henergy : ∀ j,0≤e j)
      (hgraph : ∀ j,FriedrichsGraph N (basis j:AutomorphicSpace N) ((e j:ℂ) • (basis j:AutomorphicSpace N))),
      Countable κ ∧ (∀ a b : ℝ,(principalWindowIndices e a b).Finite) ∧
      ∀ σ : ℝ,σ^2=1 → ∀ ε : ℝ → ℝ,(∀ᶠ t in atTop,0<ε t ∧ ε t≤1) →
        Tendsto (fun t => ε t*slowScale t) atTop atTop →
        Tendsto (fun t =>
          (Module.finrank ℂ (LinearMap.range (cuspWindowParity N hN basis e henergy hgraph t (t+ε t) σ)):ℝ)/(t*ε t))
          atTop (𝓝 ((quotientMeasure N).real univ/(4*Real.pi))) := by
  let : NeZero N := ⟨hN.ne'⟩
  obtain ⟨κ,basis,e,hκ,he,hgraph,hfinite,_⟩ := exists_cusp_spectrum_short_interval_weyl N hN
  refine ⟨κ,basis,e,he,hgraph,hκ,hfinite,?_⟩
  intro σ hσ ε hε hproduct
  exact cuspParityWindow_short_interval_weyl N hN basis e he hgraph σ hσ ε hε hproduct

#print axioms cuspParityWindow_short_interval_weyl
#print axioms exists_cusp_spectrum_parity_short_weyl

end QuantitativeMaass
