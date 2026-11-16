module

public import QuantitativeMaassSharpWindowLimitV1
public import QuantitativeMaassTrimmedLogPowerSpectrumV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology SchwartzMap FourierTransform InnerProductSpace

namespace QuantitativeMaass

/-- Sharp principal-window LV lower bound with the full parity coefficient.
The fixed degree is chosen before parity and before the width function.
The proof constructs its positive smoothing kernel and removes smoothing. -/
theorem exists_parity_LV_sharp_window_lower {κ : Type*}
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (henergy : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (basis j:AutomorphicSpace N) ((e j:ℂ) • (basis j:AutomorphicSpace N)))
    (δ : ℝ) (hδ : 0<δ) :
    ∃ d : ℕ,0<d ∧ ∀ (σ : ℝ),σ^2=1 → ∀ ε : ℝ → ℝ,
      (∀ᶠ t in atTop,0<ε t ∧ ε t≤1) →
      Tendsto (fun t => ε t*slowScale t) atTop atTop →
      ∀ᶠ t in atTop,(quotientMeasure N).real univ/(4*Real.pi)-δ<
        principalWindowWeight e (fun j =>
          (inner ℂ (actualLVFilter N p hN hpN a b hab d (parityProjection N σ (basis j:AutomorphicSpace N)))
            (parityProjection N σ (basis j:AutomorphicSpace N))).re) t (t+ε t)/(t*ε t) := by
  obtain ⟨d,hd,hbound⟩ := exists_windowParity_actualLV_trimmed_logPower_spectral_lower
    N p hN hpN hNp hpres a b hab basis e henergy hgraph (δ/2) (by positivity)
  obtain ⟨K,hK,he,hm,hc⟩ := exists_positive_bandlimited_window_kernel
  have ho : Orthonormal ℂ (fun j => (basis j:AutomorphicSpace N)) :=
    basis.orthonormal.comp_linearIsometry (localCuspidalSpace N hN).subtypeₗᵢ
  refine ⟨d,hd,?_⟩
  intro σ hσ ε hε hproduct
  let w := fun j => (inner ℂ
    (actualLVFilter N p hN hpN a b hab d (parityProjection N σ (basis j:AutomorphicSpace N)))
    (parityProjection N σ (basis j:AutomorphicSpace N))).re
  have hw (j : κ) : w j∈Icc (0:ℝ) 1 := actualLVFilter_parity_unit_weight
    N p hN hpN hNp hpres a b hab d σ hσ _ (basis j).property (ho.norm_eq_one j)
  have hl := hbound σ hσ K he hc hK hm UpperHalfPlane.I ε hε hproduct (1/2) (by norm_num) (by norm_num)
  have hu := window_weighted_sharp_eventual N hN (fun j => (basis j:AutomorphicSpace N))
    ho (fun j => (basis j).property) e henergy hgraph w hw K he hc hK hm ε hε hproduct
    (1/2) (by norm_num) (by norm_num) (δ/2) (by positivity)
  filter_upwards [hl,hu] with t hlt hut
  change _<principalWindowWeight e w t (t+ε t)/(t*ε t)
  change (quotientMeasure N).real univ/(4*Real.pi)-δ/2<
    (∑' j,‖smoothPacketMultiplier (windowTimeSchwartz K hc (logPowerRadius (1/2) t)
      (logPowerRadius_pos (1/2) t) (t+logPowerMargin (1/2) t)
      (t+ε t-logPowerMargin (1/2) t)) (e j)‖^2*w j)/(t*ε t) at hlt
  linarith only [hlt,hut]

/-- A countable genuine cusp energy basis, finite literal principal windows,
and a sharp LV lower bound are all constructed from the level and auxiliary
prime data. No trace, spectral-count or smoothing assumptions remain. -/
theorem exists_constructed_parity_LV_sharp_window_lower
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1) :
    ∃ (κ : Type) (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ),
      Countable κ ∧ (∀ j,0≤e j) ∧
      (∀ j,FriedrichsGraph N (basis j:AutomorphicSpace N) ((e j:ℂ) • (basis j:AutomorphicSpace N))) ∧
      (∀ u v : ℝ,(principalWindowIndices e u v).Finite) ∧
      ∀ δ : ℝ,0<δ → ∃ d : ℕ,0<d ∧ ∀ (σ : ℝ),σ^2=1 → ∀ ε : ℝ → ℝ,
        (∀ᶠ t in atTop,0<ε t ∧ ε t≤1) →
        Tendsto (fun t => ε t*slowScale t) atTop atTop →
        ∀ᶠ t in atTop,(quotientMeasure N).real univ/(4*Real.pi)-δ<
          principalWindowWeight e (fun j =>
            (inner ℂ (actualLVFilter N p hN hpN a b hab d (parityProjection N σ (basis j:AutomorphicSpace N)))
              (parityProjection N σ (basis j:AutomorphicSpace N))).re) t (t+ε t)/(t*ε t) := by
  obtain ⟨κ,basis,e,henergy,hgraph,_⟩ := QuantitativeArithmeticMaassCuspBand.exists_cuspidal_energy_basis N hN
  have ho : Orthonormal ℂ (fun j => (basis j:AutomorphicSpace N)) :=
    basis.orthonormal.comp_linearIsometry (localCuspidalSpace N hN).subtypeₗᵢ
  refine ⟨κ,basis,e,cuspidal_basis_countable N hN basis,henergy,hgraph,?_,?_⟩
  · intro u v
    exact principalWindowIndices_finite N hN _ ho (fun j => (basis j).property) e henergy hgraph u v
  · intro δ hδ
    exact exists_parity_LV_sharp_window_lower N p hN hpN hNp hpres a b hab basis e henergy hgraph δ hδ

#print axioms exists_parity_LV_sharp_window_lower
#print axioms exists_constructed_parity_LV_sharp_window_lower

end QuantitativeMaass
