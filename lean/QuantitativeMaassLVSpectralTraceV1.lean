module

public import QuantitativeMaassCuspidalTraceIdentityV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped ENNReal ContDiff InnerProductSpace

namespace QuantitativeMaass

/-- Scaling a positive quadratic form multiplies it by the scalar norm squared. -/
theorem positive_quadratic_smul {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (D : H →L[ℂ] H) (hD : 0≤D)
    (α : ℂ) (v : H) :
    (inner ℂ (D (α • v)) (α • v)).re=‖α‖^2*(inner ℂ (D v) v).re := by
  rw [←positive_sqrt_norm_square D hD, map_smul,norm_smul,mul_pow,
    positive_sqrt_norm_square D hD]

/-- LV diagonal weights lie in the unit interval on every unit cusp vector;
no simultaneous Hecke eigenbasis is needed. -/
theorem actualLVFilter_cusp_weight_bounds
    (N p : ℕ) [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a d : ℤ) (had : (p:ℤ)*a+(N:ℤ)*d=1) (k : ℕ)
    (v : AutomorphicSpace N) (hv : v∈localCuspidalSpace N hN) (hn : ‖v‖=1) :
    0≤(inner ℂ (actualLVFilter N p hN hpN a d had k v) v).re ∧
      (inner ℂ (actualLVFilter N p hN hpN a d had k v) v).re≤1 := by
  have h := actualLVFilter_quadratic_bounds N p hN hpN hNp hpres a d had k v
  have hp : localCuspidalProjection N hN v=v := Submodule.starProjection_eq_self_iff.mpr hv
  simpa only [hp,hn,one_pow] using h

/-- The actual geometric LV kernel integral is the scalar smoothed cuspidal
spectrum with its actual nonnegative LV weights. Exceptional energies are
included through signedCosine in smoothPacketMultiplier. -/
theorem actualLVFilter_kernel_trace_eq_weighted_spectrum {ι κ : Type*} [Countable ι]
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a d : ℤ) (had : (p:ℤ)*a+(N:ℤ)*d=1) (k : ℕ)
    (b : HilbertBasis ι ℂ (AutomorphicSpace N))
    (c : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (he : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (c j:AutomorphicSpace N) ((e j:ℂ) • (c j:AutomorphicSpace N)))
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    (∫⁻ x,ENNReal.ofReal ((inner ℂ
      (actualLVFilter N p hN hpN a d had k
        (poincareSeedVector N (radialSeed (abelProfile F) (abelProfile_smooth F hF hc)
          x R hR (abelProfile_support F _ hs))))
      (poincareSeedVector N (radialSeed (abelProfile F) (abelProfile_smooth F hF hc)
        x R hR (abelProfile_support F _ hs)))).re) ∂quotientMeasure N)=
      ∑' j,ENNReal.ofReal (‖smoothPacketMultiplier (coshTimeTest F) (e j)‖^2 *
        (inner ℂ (actualLVFilter N p hN hpN a d had k (c j:AutomorphicSpace N))
          (c j:AutomorphicSpace N)).re) := by
  rw [actualLVFilter_kernel_trace_eq_cusp_basis N p hN hpN hNp hpres a d had k
    b c F hF hc hr R hR hs]
  apply tsum_congr
  intro j
  change ENNReal.ofReal ((inner ℂ
    (actualLVFilter N p hN hpN a d had k
      (Wave.shiftedQuotientWavePacket N (coshTimeTest F) (coshTimeTest_waveWeight F hF R hR hs)
        (c j:AutomorphicSpace N)))
    (Wave.shiftedQuotientWavePacket N (coshTimeTest F) (coshTimeTest_waveWeight F hF R hR hs)
      (c j:AutomorphicSpace N))).re)=_
  rw [Wave.shiftedQuotientWavePacket_eigen N (coshTimeTest F) _ (he j) (hgraph j),
    positive_quadratic_smul _ (actualLVFilter_order N p hN hpN a d had k).1]
  rfl

/-- The actual weighted spectral sum is finite, not merely formally equal to an integral. -/
theorem actualLVFilter_weighted_spectrum_finite {ι κ : Type*} [Countable ι]
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a d : ℤ) (had : (p:ℤ)*a+(N:ℤ)*d=1) (k : ℕ)
    (b : HilbertBasis ι ℂ (AutomorphicSpace N))
    (c : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (he : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (c j:AutomorphicSpace N) ((e j:ℂ) • (c j:AutomorphicSpace N)))
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    (∑' j,ENNReal.ofReal (‖smoothPacketMultiplier (coshTimeTest F) (e j)‖^2 *
        (inner ℂ (actualLVFilter N p hN hpN a d had k (c j:AutomorphicSpace N))
          (c j:AutomorphicSpace N)).re))<(∞:ℝ≥0∞) := by
  rw [←actualLVFilter_kernel_trace_eq_weighted_spectrum N p hN hpN hNp hpres a d had k
    b c e he hgraph F hF hc hr R hR hs]
  exact actualLVFilter_kernel_trace_finite_of_cusp_basis N p hN hpN hNp hpres a d had k
    b c e he hgraph F hF hc hr R hR hs

#print axioms positive_quadratic_smul
#print axioms actualLVFilter_cusp_weight_bounds
#print axioms actualLVFilter_kernel_trace_eq_weighted_spectrum
#print axioms actualLVFilter_weighted_spectrum_finite

end QuantitativeMaass
