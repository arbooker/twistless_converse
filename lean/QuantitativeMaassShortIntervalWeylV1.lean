module

public import QuantitativeMaassSharpCountUpperV1
public import QuantitativeMaassSharpCountExistenceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open QuantitativeArithmeticMaassCuspBand
open scoped Topology InnerProductSpace

namespace QuantitativeMaass

/-- The sharp short-interval Weyl law for the actual complete cusp spectrum
at every positive level, with the original triple-logarithmic width condition. -/
theorem principal_short_interval_weyl {κ : Type*} (N : ℕ) (hN : 0<N)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (henergy : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (basis j:AutomorphicSpace N) ((e j:ℂ) • (basis j:AutomorphicSpace N)))
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => (Nat.card (principalWindowIndices e t (t+ε t)):ℝ)/(t*ε t)) atTop
      (𝓝 ((quotientMeasure N).real univ/(2*Real.pi))) := by
  have ho : Orthonormal ℂ (fun j => (basis j:AutomorphicSpace N)) :=
    basis.orthonormal.comp_linearIsometry (localCuspidalSpace N hN).subtypeₗᵢ
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hh := principal_sharp_count_lower_any_level N hN basis e henergy hgraph ε hε hproduct
      ((quotientMeasure N).real univ/(2*Real.pi)-a) (sub_pos.mpr ha)
    simpa only [sub_sub_cancel] using hh
  · intro b hb
    have hh := principal_sharp_count_eventual_upper N hN _ ho (fun j => (basis j).property)
      e henergy hgraph ε hε hproduct (b-(quotientMeasure N).real univ/(2*Real.pi)) (sub_pos.mpr hb)
    simpa only [add_sub_cancel] using hh

/-- An actual countable cusp eigenbasis, finite sharp windows, and the complete
short-interval Weyl law are constructed at every positive level. -/
theorem exists_cusp_spectrum_short_interval_weyl (N : ℕ) (hN : 0<N) :
    ∃ (κ : Type) (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ),
      Countable κ ∧ (∀ j,0≤e j) ∧
      (∀ j,FriedrichsGraph N (basis j:AutomorphicSpace N) ((e j:ℂ) • (basis j:AutomorphicSpace N))) ∧
      (∀ a b : ℝ,(principalWindowIndices e a b).Finite) ∧
      ∀ ε : ℝ → ℝ,(∀ᶠ t in atTop,0<ε t ∧ ε t≤1) →
        Tendsto (fun t => ε t*slowScale t) atTop atTop →
        Tendsto (fun t => (Nat.card (principalWindowIndices e t (t+ε t)):ℝ)/(t*ε t)) atTop
          (𝓝 ((quotientMeasure N).real univ/(2*Real.pi))) := by
  obtain ⟨κ,basis,e,hκ,he,hgraph,hfinite,_⟩ := exists_cusp_spectrum_sharp_lower N hN
  refine ⟨κ,basis,e,hκ,he,hgraph,hfinite,?_⟩
  intro ε hε hproduct
  exact principal_short_interval_weyl N hN basis e he hgraph ε hε hproduct

#print axioms principal_short_interval_weyl
#print axioms exists_cusp_spectrum_short_interval_weyl

end QuantitativeMaass
