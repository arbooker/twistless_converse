module

public import QuantitativeMaassTimeTranslateCarrierV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff SchwartzMap FourierTransform

namespace QuantitativeMaass

/-- Translation in a compact time weight transfers to the continuous vector
kernel in the Bochner integral. -/
theorem compact_time_translate_pairing {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (w : ℝ → E) (hw : Continuous w) (s : ℝ) :
    (∫ u,evenTimeTranslate s f u • w u)=
      (1/2:ℂ) • ((∫ u,f u • w (s+u))+(∫ u,f u • w (-s+u))) := by
  have hm : HasCompactSupport (fun u => f (u-s)) := by
    have hh : (fun u => f (u-s))=f ∘ (Homeomorph.addRight (-s)) := by
      funext u
      change f (u-s)=f (u+ -s)
      rw [sub_eq_add_neg]
    rw [hh]
    exact hc.comp_homeomorph (Homeomorph.addRight (-s))
  have hp : HasCompactSupport (fun u => f (u+s)) := hc.comp_homeomorph (Homeomorph.addRight s)
  have him : Integrable (fun u => f (u-s) • w u) :=
    ((hf.comp (continuous_id.sub continuous_const)).smul hw).integrable_of_hasCompactSupport hm.smul_right
  have hip : Integrable (fun u => f (u+s) • w u) :=
    ((hf.comp (continuous_id.add continuous_const)).smul hw).integrable_of_hasCompactSupport hp.smul_right
  have hfun (u : ℝ) : evenTimeTranslate s f u • w u=
      (1/2:ℂ) • (f (u-s) • w u+f (u+s) • w u) := by
    rw [smul_add,smul_smul,smul_smul,← add_smul]
    congr 1
    unfold evenTimeTranslate
    ring
  simp_rw [hfun]
  rw [integral_smul,integral_add him hip]
  have hminus : (∫ u,f (u-s) • w u)=∫ u,f u • w (s+u) := by
    have hh := integral_add_left_eq_self (μ := volume) (fun u : ℝ => f (u-s) • w u) s
    simpa only [add_sub_cancel_left] using hh.symm
  have hplus : (∫ u,f (u+s) • w u)=∫ u,f u • w (-s+u) := by
    have hh := integral_add_left_eq_self (μ := volume) (fun u : ℝ => f (u+s) • w u) (-s)
    simpa only [neg_add_cancel_comm] using hh.symm
  rw [hminus,hplus]

/-- Symmetric translation is exactly one actual quotient cosine wave acting
on the compact even packet, as an operator on the full Hilbert space. -/
theorem evenTimeTranslate_wavePacket (N : ℕ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (he : Function.Even f) (s : ℝ) :
    Wave.shiftedQuotientWavePacket N (evenTimeTranslate s f)
      (compactSmoothWaveWeight _ (evenTimeTranslate_smooth s f hf) (evenTimeTranslate_compact s f hc))=
    Wave.shiftedQuotientWave N s * Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f hf hc) := by
  apply ContinuousLinearMap.ext
  intro v
  change (∫ u,evenTimeTranslate s f u • Wave.shiftedQuotientWave N u v)=
    Wave.shiftedQuotientWave N s (Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f hf hc) v)
  rw [compact_time_translate_pairing f hf.continuous hc _ (Wave.shiftedQuotientWave_stronglyContinuous N v) s,
    ← shiftedWave_even_packet N f hf hc he s v,← shiftedWave_even_packet N f hf hc he (-s) v,
    Wave.shiftedQuotientWave_neg]
  rw [← two_smul ℂ,smul_smul]
  norm_num

/-- On scalar cosine packets the same translation has precisely the cosine
spectral multiplier. No spectral expansion of the quotient is assumed. -/
theorem evenTimeTranslate_cosinePacket (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (s r : ℝ) :
    cosinePacket (evenTimeTranslate s f) r=(Real.cos (s*r):ℂ)*cosinePacket f r := by
  have hh := compact_time_translate_pairing f hf hc (fun u => (Real.cos (u*r):ℂ)) (by fun_prop) s
  change (∫ u,evenTimeTranslate s f u*(Real.cos (u*r):ℂ))=
    (Real.cos (s*r):ℂ)*(∫ u,f u*(Real.cos (u*r):ℂ))
  simp only [smul_eq_mul] at hh
  rw [hh]
  have hi (a : ℝ) : Integrable (fun u => f u*(Real.cos ((a+u)*r):ℂ)) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hc.mul_right
  rw [← integral_add (hi s) (hi (-s)),← integral_const_mul,← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun u => by
    dsimp only
    rw [show (s+u)*r=s*r+u*r by ring,show (-s+u)*r= -(s*r)+u*r by ring,
      Real.cos_add,Real.cos_add,Real.cos_neg,Real.sin_neg]
    push_cast
    ring)

/-- The translated compact even time test retains the genuine spherical
identity density, multiplied by its actual cosine factor. -/
theorem evenTimeTranslate_spherical_identity (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (he : Function.Even f) (hc : HasCompactSupport f) (s : ℝ) :
    abelProfile (evenCoshLift (evenTimeTranslate s f)) 1=
      (1/(4*Real.pi):ℂ)*(∫ r : ℝ,(Real.cos (s*r):ℂ)*cosinePacket f r*
        ((r*Real.tanh (Real.pi*r):ℝ):ℂ)) := by
  rw [abelProfile_evenCoshLift_fourier _ (evenTimeTranslate_smooth s f hf)
    (evenTimeTranslate_even s f he) (evenTimeTranslate_compact s f hc)]
  simp_rw [evenTimeTranslate_cosinePacket f hf.continuous hc]

/-- The translated square packet is the actual wave inserted between the
original smoothing operators. This is the operator needed in mixed traces. -/
theorem evenTimeTranslate_timeSquare_wavePacket (N : ℕ) (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ → ℂ)) (he : Function.Even f) (s : ℝ) :
    Wave.shiftedQuotientWavePacket N (evenTimeTranslate s (timeConvolution f f))
      (compactSmoothWaveWeight _ (evenTimeTranslate_smooth s _ ((timeConvolution f f).smooth ⊤))
        (evenTimeTranslate_compact s _ (timeConvolution_compact f f hc hc)))=
      Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f (f.smooth ⊤) hc)*
        Wave.shiftedQuotientWave N s*
        Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f (f.smooth ⊤) hc) := by
  rw [evenTimeTranslate_wavePacket N _ ((timeConvolution f f).smooth ⊤)
    (timeConvolution_compact f f hc hc) (timeConvolution_even f f he he),
    timeConvolution_wavePacket N f f hc hc he,← mul_assoc]
  let A := Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f (f.smooth ⊤) hc)
  have hh := Wave.shiftedQuotientWave_commute_of_resolvent N A
    (Wave.shiftedQuotientWavePacket_commute_resolvent N f _) s
  exact congrArg (fun B : AutomorphicSpace N →L[ℂ] AutomorphicSpace N => B*A) hh.symm.eq

#print axioms evenTimeTranslate_timeSquare_wavePacket

#print axioms compact_time_translate_pairing
#print axioms evenTimeTranslate_wavePacket
#print axioms evenTimeTranslate_cosinePacket
#print axioms evenTimeTranslate_spherical_identity

end QuantitativeMaass
