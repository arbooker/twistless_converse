module

public import QuantitativeMaassWindowIdentityTermV1
public import Mathlib.MeasureTheory.Group.Prod

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology SchwartzMap ContDiff Convolution FourierTransform

namespace QuantitativeMaass

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A continuous vector-valued kernel with two compact scalar factors is
integrable on the time plane. -/
theorem compact_time_pair_integrable (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (w : ℝ × ℝ → E) (hw : Continuous w) :
    Integrable (fun p : ℝ × ℝ => (f p.1*g p.2) • w p) (volume.prod volume) := by
  have hc : HasCompactSupport (fun p : ℝ × ℝ => (f p.1*g p.2) • w p) := by
    apply HasCompactSupport.intro (hfc.isCompact.prod hgc.isCompact)
    intro p hp
    by_cases hpf : p.1 ∈ tsupport f
    · have hpg : p.2 ∉ tsupport g := fun h => hp ⟨hpf,h⟩
      rw [image_eq_zero_of_notMem_tsupport hpg, mul_zero, zero_smul]
    · rw [image_eq_zero_of_notMem_tsupport hpf, zero_mul, zero_smul]
  exact ((hf.comp continuous_fst).mul (hg.comp continuous_snd) |>.smul hw).integrable_of_hasCompactSupport hc

/-- Fubini for time convolution against an arbitrary continuous vector kernel.
No global integrability assumption on the vector kernel is needed. -/
theorem compact_time_convolution_integral [CompleteSpace E] (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) (w : ℝ → E) (hw : Continuous w) :
    (∫ u : ℝ, ((f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) u) • w u) =
      ∫ s : ℝ, ∫ t : ℝ, (f s*g t) • w (s+t) := by
  have hG := compact_time_pair_integrable f g hf hg hfc hgc
    (fun p : ℝ × ℝ => w (p.1+p.2)) (hw.comp (continuous_fst.add continuous_snd))
  have hH : Integrable (Function.uncurry (fun u s : ℝ => (f s*g (u-s)) • w u))
      (volume.prod volume) := by
    have hi := (measurePreserving_prod_sub_swap (volume : Measure ℝ) volume).integrable_comp_of_integrable hG
    simpa only [Function.comp_def, Function.uncurry_def, add_sub_cancel] using hi
  calc
    _ = ∫ u : ℝ, ∫ s : ℝ, (f s*g (u-s)) • w u := by
      simp only [convolution_def, ContinuousLinearMap.mul_apply', integral_smul_const]
    _ = ∫ s : ℝ, ∫ u : ℝ, (f s*g (u-s)) • w u := integral_integral_swap hH
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with s
      have h := integral_add_left_eq_self (μ := volume) (fun u : ℝ => (f s*g (u-s)) • w u) s
      simpa only [add_sub_cancel_left] using h.symm

theorem shiftedWave_translated_packet_integrable (N : ℕ) (g : ℝ → ℂ)
    (hg : Continuous g) (hc : HasCompactSupport g) (s : ℝ) (v : AutomorphicSpace N) :
    Integrable (fun t : ℝ => g t • Wave.shiftedQuotientWave N (s+t) v) := by
  have hw := (Wave.shiftedQuotientWave_stronglyContinuous N v).comp
    (show Continuous (fun t : ℝ => s+t) from continuous_const.add continuous_id)
  exact (hg.smul hw).integrable_of_hasCompactSupport hc.smul_right

/-- One actual wave operator acting on an even packet is time translation. -/
theorem shiftedWave_even_packet (N : ℕ) (g : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (he : Function.Even g)
    (s : ℝ) (v : AutomorphicSpace N) :
    Wave.shiftedQuotientWave N s
      (Wave.shiftedQuotientWavePacket N g (compactSmoothWaveWeight g hg hc) v) =
      ∫ t : ℝ, g t • Wave.shiftedQuotientWave N (s+t) v := by
  let W := Wave.shiftedQuotientWave N
  have hplus := shiftedWave_translated_packet_integrable N g hg.continuous hc s v
  have hminus : Integrable (fun t : ℝ => g t • W (s-t) v) := by
    have hw := (Wave.shiftedQuotientWave_stronglyContinuous N v).comp
      (show Continuous (fun t : ℝ => s-t) from continuous_const.sub continuous_id)
    exact (hg.continuous.smul hw).integrable_of_hasCompactSupport hc.smul_right
  have hprod : Integrable (fun t : ℝ => g t • W s (W t v)) := by
    have h := (W s).integrable_comp
      (Wave.shiftedQuotientWave_packet_integrable N (compactSmoothWaveWeight g hg hc) v)
    simpa only [Function.comp_def, map_smul] using h
  have hm : (∫ t : ℝ, g t • W (s-t) v)=∫ t : ℝ, g t • W (s+t) v := by
    rw [← integral_neg_eq_self (fun t : ℝ => g t • W (s-t) v)]
    simp only [sub_neg_eq_add]
    apply integral_congr_ae
    filter_upwards with t
    rw [he t]
  have hp (t : ℝ) : g t • W (s+t) v+g t • W (s-t) v =
      g t • W s (W t v)+g t • W s (W t v) := by
    have h := congrArg (fun A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N => A v)
      (Wave.shiftedQuotientWave_cosine N s t)
    change W (s+t) v+W (s-t) v=W s (W t v)+W s (W t v) at h
    simpa only [smul_add] using congrArg (fun z : AutomorphicSpace N => g t • z) h
  have h := congrArg (fun z : ℝ → AutomorphicSpace N => ∫ t,z t) (funext hp)
  rw [integral_add hplus hminus, integral_add hprod hprod, hm] at h
  have hmap : W s (Wave.shiftedQuotientWavePacket N g (compactSmoothWaveWeight g hg hc) v)=
      ∫ t : ℝ, g t • W s (W t v) := by
    rw [Wave.shiftedQuotientWavePacket_apply, ← (W s).integral_comp_comm
      (Wave.shiftedQuotientWave_packet_integrable N (compactSmoothWaveWeight g hg hc) v)]
    simp only [map_smul, W]
  change W s _=_
  rw [hmap]
  apply (smul_right_injective (AutomorphicSpace N) (by norm_num : (2:ℂ)≠0))
  simpa only [two_smul, W] using h.symm

/-- Time convolution represents composition of the actual quotient packets.
This is an operator identity on the full Hilbert space, not just eigenvectors. -/
theorem timeConvolution_wavePacket (N : ℕ) (f g : SchwartzMap ℝ ℂ)
    (hfc : HasCompactSupport (f : ℝ → ℂ)) (hgc : HasCompactSupport (g : ℝ → ℂ))
    (he : Function.Even g) :
    Wave.shiftedQuotientWavePacket N (timeConvolution f g)
      (compactSmoothWaveWeight _ ((timeConvolution f g).smooth ⊤) (timeConvolution_compact f g hfc hgc)) =
    Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight _ (f.smooth ⊤) hfc) *
      Wave.shiftedQuotientWavePacket N g (compactSmoothWaveWeight _ (g.smooth ⊤) hgc) := by
  apply ContinuousLinearMap.ext
  intro v
  change Wave.shiftedQuotientWavePacket N (timeConvolution f g)
    (compactSmoothWaveWeight _ ((timeConvolution f g).smooth ⊤) (timeConvolution_compact f g hfc hgc)) v=
    Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight _ (f.smooth ⊤) hfc)
      (Wave.shiftedQuotientWavePacket N g (compactSmoothWaveWeight _ (g.smooth ⊤) hgc) v)
  rw [Wave.shiftedQuotientWavePacket_apply, Wave.shiftedQuotientWavePacket_apply]
  simp only [timeConvolution, SchwartzMap.convolution_apply]
  rw [compact_time_convolution_integral f g f.continuous g.continuous hfc hgc
    _ (Wave.shiftedQuotientWave_stronglyContinuous N v)]
  apply integral_congr_ae
  filter_upwards with s
  rw [shiftedWave_even_packet N g (g.smooth ⊤) hgc he]
  rw [← integral_smul]
  simp only [smul_smul]

theorem timeConvolution_real (f g : SchwartzMap ℝ ℂ)
    (hf : ∀ t,star (f t)=f t) (hg : ∀ t,star (g t)=g t) (t : ℝ) :
    star (timeConvolution f g t)=timeConvolution f g t := by
  simp only [timeConvolution, SchwartzMap.convolution_apply, convolution_def,
    ContinuousLinearMap.mul_apply', Complex.star_def]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with s
  change star (f s*g (t-s))=f s*g (t-s)
  rw [star_mul, hf, hg, mul_comm]

/-- Exact support addition for time convolution. -/
theorem timeConvolution_support (f g : SchwartzMap ℝ ℂ) (R S : ℝ)
    (hf : Function.support f⊆Icc (-R) R) (hg : Function.support g⊆Icc (-S) S) :
    Function.support (timeConvolution f g)⊆Icc (-(R+S)) (R+S) := by
  intro t ht
  have hc : t ∈ Function.support ((f : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] g) := by
    simpa only [Function.mem_support, timeConvolution, SchwartzMap.convolution_apply] using ht
  obtain ⟨s,hs,u,hu,heq⟩ := support_convolution_subset (ContinuousLinearMap.mul ℂ ℂ) hc
  have hsR := hf hs
  have huS := hg hu
  rw [← heq]
  constructor <;> linarith [hsR.1,hsR.2,huS.1,huS.2]

/-- The product of two original real even packets has the actual Abel kernel
of their time convolution. It is an AE output identity for every input. -/
theorem timeConvolution_wavePacket_kernel (N : ℕ) [NeZero N] (f g : SchwartzMap ℝ ℂ)
    (hfc : HasCompactSupport (f : ℝ → ℂ)) (hgc : HasCompactSupport (g : ℝ → ℂ))
    (hfe : Function.Even f) (hge : Function.Even g)
    (hfr : ∀ t,star (f t)=f t) (hgr : ∀ t,star (g t)=g t)
    (R S : ℝ) (hR : 0≤R) (hS : 0≤S)
    (hf : Function.support f⊆Icc (-R) R) (hg : Function.support g⊆Icc (-S) S)
    (v : AutomorphicSpace N) :
    (Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight _ (f.smooth ⊤) hfc)
      (Wave.shiftedQuotientWavePacket N g (compactSmoothWaveWeight _ (g.smooth ⊤) hgc) v)).val =ᵐ[quotientMeasure N]
      (fun x => ∫ y, radialPoincareKernel N (abelProfile (evenCoshLift (timeConvolution f g))) x y*v.val y
        ∂quotientMeasure N) := by
  have h := evenWavePacket_kernel_coeFn N (timeConvolution f g) ((timeConvolution f g).smooth ⊤)
    (timeConvolution_even f g hfe hge) (timeConvolution_compact f g hfc hgc)
    (timeConvolution_real f g hfr hgr) (R+S) (add_nonneg hR hS)
    (timeConvolution_support f g R S hf hg) v
  rw [timeConvolution_wavePacket N f g hfc hgc hge] at h
  exact h

/-- The actual moving-window packet square has the time-convolution Abel
kernel, with no externally supplied support radius or kernel hypothesis. -/
theorem windowWavePacket_square_kernel (N : ℕ) [NeZero N] (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) (v : AutomorphicSpace N) :
    (windowWavePacket N K hc R hR a b (windowWavePacket N K hc R hR a b v)).val =ᵐ[quotientMeasure N]
      (fun x => ∫ y, radialPoincareKernel N
        (abelProfile (evenCoshLift (timeConvolution (windowTimeSchwartz K hc R hR a b)
          (windowTimeSchwartz K hc R hR a b)))) x y*v.val y ∂quotientMeasure N) := by
  let f := windowTimeSchwartz K hc R hR a b
  have hfe : Function.Even f := symmetricWindowTimeTest_even K he R a b
  have hfr : ∀ t,star (f t)=f t := symmetricWindowTimeTest_real K he R a b
  have hfc : HasCompactSupport (f : ℝ → ℂ) := symmetricWindowTimeTest_compact K hc R a b hR
  obtain ⟨B,hB,hs⟩ := symmetricWindowTimeTest_uniform_support K hc
  exact timeConvolution_wavePacket_kernel N f f hfc hfc hfe hfe hfr hfr
    (B*R) (B*R) (mul_nonneg hB.le hR.le) (mul_nonneg hB.le hR.le)
    (hs R hR a b) (hs R hR a b) v

end QuantitativeMaass

#print axioms QuantitativeMaass.compact_time_pair_integrable
#print axioms QuantitativeMaass.compact_time_convolution_integral
#print axioms QuantitativeMaass.shiftedWave_translated_packet_integrable
#print axioms QuantitativeMaass.shiftedWave_even_packet
#print axioms QuantitativeMaass.timeConvolution_wavePacket
#print axioms QuantitativeMaass.timeConvolution_real
#print axioms QuantitativeMaass.timeConvolution_support
#print axioms QuantitativeMaass.timeConvolution_wavePacket_kernel
#print axioms QuantitativeMaass.windowWavePacket_square_kernel
