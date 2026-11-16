module

public import QuantitativeMaassMajorantJointExcessLimitV1
public import QuantitativeMaassFullTerminalCountableV1
public import QuantitativeMaassFullNewEnergyLimitV1
public import QuantitativeMaassTotalUpperParityV1
public import QuantitativeMaassLVParityExistenceV1
public import QuantitativeMaassEulerLevelOneLimitV1

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory AsymptoticClassicalPetersson AsymptoticSectorSigns
open QuantitativeNinaMaass QuantitativeConcreteGoals
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass
open Scheduled

/-- Original Euler-product counts at all admissible levels at least two.
The certificate, cover, kernel, prime data, spectra and Hilbert bases are
constructed internally; no upper trace or excess hypothesis is assumed. -/
theorem originalMajorantWindow_claims (N : ℕ) (hN : GridAdmissibleGap.Admissible N) (hN2 : 2≤N)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    MaassWindowClaim N 0 ε ∧ MaassWindowClaim N 1 ε := by
  classical
  let : NeZero N := ⟨hN.1.ne'⟩
  obtain ⟨Q,hQ,_,⟨A⟩⟩ := FinitenessCertificate.exists_certificate N hN.1 hN.2.1 hN.2.2
  obtain ⟨P⟩ := FinitenessGlobalHeight.parameters_exist hN.1 hQ A
  let cover := jointScalarCover N hN
  obtain ⟨ι,hι,⟨b⟩⟩ := exists_countable_full_terminal_basis (AsymptoticReconstructedCount.parameters A P).ε
  let : Countable ι := hι
  obtain ⟨κ,hκ,⟨c⟩⟩ := exists_countable_cylinder_basis
  let : Countable κ := hκ
  obtain ⟨ρ,d,_⟩ := exists_hilbertBasis ℂ (completedCuspidalNewSpace N hN.1)
  obtain ⟨ρp,dp,_⟩ := exists_hilbertBasis ℂ (completedCuspidalNewParitySpace N hN.1 1)
  obtain ⟨ρm,dm,_⟩ := exists_hilbertBasis ℂ (completedCuspidalNewParitySpace N hN.1 (-1))
  choose indices ds hds using (fun e : Sector N =>
    exists_hilbertBasis ℂ (completedNewSignSpace N hN.1 (sectorCharacter N hN.1 e)))
  obtain ⟨K,hK,he,hm,hc⟩ := exists_positive_bandlimited_window_kernel
  let C := max 1 (supportRadius K hc)
  have hC : 1≤C := le_max_left _ _
  have hCs : supportRadius K hc≤C := le_max_right _ _
  let f := QuantitativeNinaMaass.originalWindowMajorant K hc ε
  let hf := originalWindowMajorant_compact K hc ε
  let hfe := originalWindowMajorant_even K he hc ε
  let hfr := originalWindowMajorant_real K he hc ε
  let R := fun t => C*radius ε t
  have hR (t : ℝ) : 0≤R t := mul_nonneg (zero_le_one.trans hC) (radius_pos ε t).le
  have hs (t : ℝ) : Function.support (f t)⊆Icc (-(R t)) (R t) :=
    originalMajorant_support_enlarged K hc ε t C hCs
  let energy := fun t => hilbertSchmidtEnergy d (completedCuspidalNewTimePacket N hN.1
    (f t) ((f t).smooth ⊤) (hf t))
  let excess := fun e t => RawOriginalWindow.jointMetricSectorExcess A hN cover P e
    (f t) (hf t) (hfe t) (R t) (hR t) (hs t)
  have henergy : Tendsto (fun t => energy t/(t*ε t)) atTop
      (𝓝 (2*AsymptoticTotalNewCorner.arithmeticCoefficient N)) :=
    originalNewWindowPacket_energy_limit N hN d dp dm K he hc hK hm ε hε hp
  obtain ⟨p,hpprime,_hgt,hpN,hNp,hpres,a,bz,hab⟩ := exists_lv_prime_data N hN.1
  let : Fact p.Prime := ⟨hpprime⟩
  have hexcess (e : Sector N) : Tendsto (fun t => excess e t/(t*ε t)) atTop (𝓝 0) :=
    originalMajorant_joint_metric_excess_limit c N p hN.1 hN hpN hNp hpres a bz hab
      (geometricCuspSpectrum N hN.1)
      (fun q => geometricCuspSpectrum (N/q.val)
        (QuantitativeArithmeticNewBandProjections.prime_quotient_pos N q.val hN.1 (Nat.prime_of_mem_primeFactors q.property)
          (Nat.dvd_of_mem_primeFactors q.property))) cover e A P hN2 C hC K hc hCs he hK hm ε hε hp
  have hsum : Tendsto (fun t => (∑ e : Sector N,excess e t)/(t*ε t)) atTop (𝓝 0) := by
    simpa only [Finset.sum_div,Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun e _ => hexcess e)
  let U := fun t => energy t+∑ e : Sector N,excess e t
  have hU : Tendsto (fun t => U t/(t*ε t)) atTop
      (𝓝 (2*AsymptoticTotalNewCorner.arithmeticCoefficient N)) := by
    simpa only [U,add_div,add_zero] using henergy.add hsum
  have hcount : ∀ᶠ t in atTop,(maassWindow N 0 t (ε t)).Finite ∧
      (maassWindow N 1 t (ε t)).Finite ∧
      ((maassWindow N 0 t (ε t)).ncard:ℝ)+((maassWindow N 1 t (ε t)).ncard:ℝ)≤U t := by
    filter_upwards [originalWindowMajorant_majorizes K he hc hK hm ε hε hp] with t ht
    exact RawOriginalWindow.bothWindow_joint_metric_count A hN cover P b c d (fun e => ↥(indices e)) ds
      t (ε t) (f t) (hf t) (hfe t) (hfr t) (R t) (hR t) (hs t) ht
  exact maassWindow_claims_of_total_upper N hN ε hε hp U hU
    (hcount.mono (fun _ h => ⟨h.1,h.2.1⟩)) (hcount.mono (fun _ h => h.2.2))

/-- Literal requested Maass window theorem, including level one. -/
theorem requestedMaassWindow : RequestedMaassWindowTheorem := by
  intro N hN σ hσ ε hε hp
  by_cases h1 : N=1
  · subst N
    exact originalLevelOneWindow_limit σ hσ ε hε hp
  · have hh := originalMajorantWindow_claims N hN (by have := hN.1; omega) ε hε hp
    rcases hσ with rfl | rfl
    · exact hh.1
    · exact hh.2

/-- The combined parity count has twice the fixed-parity coefficient. -/
theorem requestedMaassWindow_parity_sum (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    (∀ᶠ t in atTop,(maassWindow N 0 t (ε t)).Finite ∧ (maassWindow N 1 t (ε t)).Finite) ∧
    Tendsto (fun t : ℝ =>
      (((maassWindow N 0 t (ε t)).ncard+(maassWindow N 1 t (ε t)).ncard:ℕ):ℝ)/(t*ε t))
      atTop (𝓝 (2*AsymptoticTotalNewCorner.arithmeticCoefficient N)) :=
  maassWindow_parity_sum N ε
    (requestedMaassWindow N hN 0 (Or.inl rfl) ε hε hp)
    (requestedMaassWindow N hN 1 (Or.inr rfl) ε hε hp)

/-- At a fixed real parameter the literal solution count is o(r). -/
theorem requestedMaassWindow_pointwise (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    (σ : ℕ) (hσ : σ=0 ∨ σ=1) :
    (∀ᶠ r in atTop,(maassWindow N σ r 0).Finite) ∧
    Tendsto (fun r : ℝ => ((maassWindow N σ r 0).ncard:ℝ)/r) atTop (𝓝 0) :=
  maassWindow_pointwise_of_canonicalWidth N σ
    (requestedMaassWindow N hN σ hσ canonicalWidth canonicalWidth_eventually_unit
      canonicalWidth_properties.2.2)

#print axioms requestedMaassWindow_parity_sum
#print axioms requestedMaassWindow_pointwise
#print axioms originalMajorantWindow_claims
#print axioms requestedMaassWindow
end QuantitativeMaass
