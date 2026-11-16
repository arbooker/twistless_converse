module

public import QuantitativeMaassLVParitySpectrumLowerV1
public import Mathlib.NumberTheory.PrimesCongruentOne

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace ENNReal SchwartzMap FourierTransform

namespace QuantitativeMaass

/-- The auxiliary prime and all its actual branch/cuspidalizer data exist for
every positive level, by the proved supply of primes congruent to one. -/
theorem exists_lv_prime_data (N : ℕ) (hN : 0<N) :
    ∃ p : ℕ,p.Prime ∧ N<p ∧ ¬p∣N ∧ (N:ZMod p)≠0 ∧ (p:ZMod N)=1 ∧
      ∃ a b : ℤ,(p:ℤ)*a+(N:ℤ)*b=1 := by
  obtain ⟨p,hp,hgt,hmod⟩ := Nat.exists_prime_gt_modEq_one N hN.ne'
  have hnd : ¬p∣N := fun hd => (not_le_of_gt hgt) (Nat.le_of_dvd hN hd)
  have hcop : p.Coprime N := hp.coprime_iff_not_dvd.mpr hnd
  have hnz : (N:ZMod p)≠0 := fun hz => hnd ((ZMod.natCast_eq_zero_iff N p).mp hz)
  have hpres : (p:ZMod N)=1 := by
    have hh := (ZMod.natCast_eq_natCast_iff p 1 N).mpr hmod
    simpa only [Nat.cast_one] using hh
  refine ⟨p,hp,hgt,hnd,hnz,hpres,Nat.gcdA p N,Nat.gcdB p N,?_⟩
  rw [← Nat.gcd_eq_gcd_ab,hcop.gcd_eq_one,Int.natCast_one]

/-- A genuine countable cusp energy basis is constructed once. With this
basis one obtains the quantitative parity LV spectral lower bound for every
accuracy tolerance and every original admissible shrinking window. -/
theorem exists_constructed_parity_LV_spectral_lower
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1) :
    ∃ (κ : Type) (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ),
      Countable κ ∧ (∀ j,0≤e j) ∧
      (∀ j,FriedrichsGraph N (basis j:AutomorphicSpace N) ((e j:ℂ) • (basis j:AutomorphicSpace N))) ∧
      ∀ δ : ℝ,0<δ → ∃ d : ℕ,0<d ∧ ∀ (σ : ℝ),σ^2=1 →
      ∀ (K : SchwartzMap ℝ ℝ) (_he : Function.Even K)
        (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))),
        (∀ x,0≤K x) → (∫ x,K x)=1 → ∀ (_o : ℍ) (ε : ℝ → ℝ),
        (∀ᶠ t in atTop,0<ε t ∧ ε t≤1) →
        Tendsto (fun t => ε t*slowScale t) atTop atTop →
        ∀ᶠ t in atTop,(quotientMeasure N).real univ/(4*Real.pi)-δ<
          (∑' j,‖smoothPacketMultiplier (windowTimeSchwartz K hc (positiveWindowRadius ε t)
            (positiveWindowRadius_pos ε t) t (t+ε t)) (e j)‖^2 *
            (inner ℂ (actualLVFilter N p hN hpN a b hab d (parityProjection N σ (basis j:AutomorphicSpace N)))
              (parityProjection N σ (basis j:AutomorphicSpace N))).re)/(t*ε t) := by
  obtain ⟨κ,basis,e,henergy,hgraph,_⟩ := QuantitativeArithmeticMaassCuspBand.exists_cuspidal_energy_basis N hN
  refine ⟨κ,basis,e,cuspidal_basis_countable N hN basis,henergy,hgraph,?_⟩
  intro δ hδ
  exact exists_windowParity_actualLV_spectral_lower N p hN hpN hNp hpres a b hab basis e henergy hgraph δ hδ

#print axioms exists_lv_prime_data
#print axioms exists_constructed_parity_LV_spectral_lower

end QuantitativeMaass
