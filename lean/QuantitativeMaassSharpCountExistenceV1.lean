module

public import QuantitativeMaassSharpCountLowerV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology InnerProductSpace

namespace QuantitativeMaass

/-- The actual sharp cusp count lower coefficient holds at every positive
level; the required auxiliary prime and Bezout data are internally supplied. -/
theorem principal_sharp_count_lower_any_level {κ : Type*} (N : ℕ) (hN : 0<N)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (henergy : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (basis j:AutomorphicSpace N) ((e j:ℂ) • (basis j:AutomorphicSpace N)))
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (η : ℝ) (hη : 0<η) :
    ∀ᶠ t in atTop,(quotientMeasure N).real univ/(2*Real.pi)-η<
      (Nat.card (principalWindowIndices e t (t+ε t)):ℝ)/(t*ε t) := by
  let : NeZero N := ⟨hN.ne'⟩
  obtain ⟨p,hp,_hgt,hpN,hNp,hpres,a,b,hab⟩ := exists_lv_prime_data N hN
  let : Fact p.Prime := ⟨hp⟩
  exact principal_sharp_count_eventual_lower N p hN hpN hNp hpres a b hab basis e henergy hgraph
    ε hε hproduct η hη

/-- An actual countable cusp energy basis with finite sharp windows and the
full-volume sharp lower asymptotic is constructed at every positive level.
The matching sharp upper asymptotic is a separate theorem still required. -/
theorem exists_cusp_spectrum_sharp_lower (N : ℕ) (hN : 0<N) :
    ∃ (κ : Type) (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ),
      Countable κ ∧ (∀ j,0≤e j) ∧
      (∀ j,FriedrichsGraph N (basis j:AutomorphicSpace N) ((e j:ℂ) • (basis j:AutomorphicSpace N))) ∧
      (∀ a b : ℝ,(principalWindowIndices e a b).Finite) ∧
      ∀ ε : ℝ → ℝ,(∀ᶠ t in atTop,0<ε t ∧ ε t≤1) →
        Tendsto (fun t => ε t*slowScale t) atTop atTop →
        ∀ η : ℝ,0<η → ∀ᶠ t in atTop,(quotientMeasure N).real univ/(2*Real.pi)-η<
          (Nat.card (principalWindowIndices e t (t+ε t)):ℝ)/(t*ε t) := by
  let : NeZero N := ⟨hN.ne'⟩
  obtain ⟨κ,basis,e,henergy,hgraph,_⟩ := QuantitativeArithmeticMaassCuspBand.exists_cuspidal_energy_basis N hN
  have ho : Orthonormal ℂ (fun j => (basis j:AutomorphicSpace N)) :=
    basis.orthonormal.comp_linearIsometry (localCuspidalSpace N hN).subtypeₗᵢ
  refine ⟨κ,basis,e,cuspidal_basis_countable N hN basis,henergy,hgraph,?_,?_⟩
  · intro a b
    exact principalWindowIndices_finite N hN _ ho (fun j => (basis j).property) e henergy hgraph a b
  · intro ε hε hproduct η hη
    exact principal_sharp_count_lower_any_level N hN basis e henergy hgraph ε hε hproduct η hη

#print axioms principal_sharp_count_lower_any_level
#print axioms exists_cusp_spectrum_sharp_lower

end QuantitativeMaass
