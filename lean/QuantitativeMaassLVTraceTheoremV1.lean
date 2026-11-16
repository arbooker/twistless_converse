module

public import QuantitativeMaassCountableBasisV1
public import QuantitativeArithmeticMaassCuspidalEigenbasisV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped ENNReal InnerProductSpace ContDiff

namespace QuantitativeMaass

/-- Ordinary integrability of the literal LV kernel, with the actual cusp eigenbasis constructed internally. -/
theorem actualLVFilter_kernel_integrable_unconditional 
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a d : ℤ) (had : (p:ℤ)*a+(N:ℤ)*d=1) (k : ℕ)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    Integrable (fun x => (inner ℂ
      (actualLVFilter N p hN hpN a d had k
        (poincareSeedVector N (radialSeed (abelProfile F) (abelProfile_smooth F hF hc)
          x R hR (abelProfile_support F _ hs))))
      (poincareSeedVector N (radialSeed (abelProfile F) (abelProfile_smooth F hF hc)
        x R hR (abelProfile_support F _ hs)))).re) (quotientMeasure N) := by
  obtain ⟨κ,c,e,he,hgraph,_⟩ := QuantitativeArithmeticMaassCuspBand.exists_cuspidal_energy_basis N hN
  exact actualLVFilter_kernel_integrable_of_cusp_basis N p hN hpN hNp hpres a d had k
    c e he hgraph F hF hc hr R hR hs

/-- A genuine countable cusp energy basis realizes the convergent scalar LV trace. No completeness, counting, trace, or eigenbasis premise is assumed. -/
theorem exists_actualLVFilter_spectral_trace 
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a d : ℤ) (had : (p:ℤ)*a+(N:ℤ)*d=1) (k : ℕ)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    ∃ (κ : Type) (c : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ),
      Countable κ ∧ (∀ j,0≤e j) ∧
      (∀ j,FriedrichsGraph N (c j:AutomorphicSpace N) ((e j:ℂ) • (c j:AutomorphicSpace N))) ∧
      Summable (fun j => ‖smoothPacketMultiplier (coshTimeTest F) (e j)‖^2 *
        (inner ℂ (actualLVFilter N p hN hpN a d had k (c j:AutomorphicSpace N))
          (c j:AutomorphicSpace N)).re) ∧
    (∫ x, (inner ℂ
      (actualLVFilter N p hN hpN a d had k
        (poincareSeedVector N (radialSeed (abelProfile F) (abelProfile_smooth F hF hc)
          x R hR (abelProfile_support F _ hs))))
      (poincareSeedVector N (radialSeed (abelProfile F) (abelProfile_smooth F hF hc)
        x R hR (abelProfile_support F _ hs)))).re ∂quotientMeasure N)=∑' j,‖smoothPacketMultiplier (coshTimeTest F) (e j)‖^2 *
        (inner ℂ (actualLVFilter N p hN hpN a d had k (c j:AutomorphicSpace N))
          (c j:AutomorphicSpace N)).re := by
  obtain ⟨κ,c,e,he,hgraph,_⟩ := QuantitativeArithmeticMaassCuspBand.exists_cuspidal_energy_basis N hN
  obtain ⟨ι,hι,⟨b⟩⟩ := exists_countable_automorphic_basis N
  let : Countable ι := hι
  refine ⟨κ,c,e,cuspidal_basis_countable N hN c,he,hgraph,?_,?_⟩
  · exact actualLVFilter_weighted_spectrum_summable N p hN hpN hNp hpres a d had k
      b c e he hgraph F hF hc hr R hR hs
  · exact actualLVFilter_real_trace_eq_weighted_spectrum_of_cusp_basis N p hN hpN hNp hpres a d had k
      c e he hgraph F hF hc hr R hR hs

#print axioms actualLVFilter_kernel_integrable_unconditional
#print axioms exists_actualLVFilter_spectral_trace

end QuantitativeMaass
