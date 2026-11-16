module

public import QuantitativeMaassReflectionWaveV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff SchwartzMap

namespace QuantitativeMaass

/-- Commutation with compact even real packets implies commutation with
the genuine unsmoothed shifted wave. -/
theorem timePacket_commuting_wave (N : ℕ) (U : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (hU : ∀ (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (_he : Function.Even f)
      (hc : HasCompactSupport f) (_hr : ∀ s,star (f s)=f s) (R : ℝ) (_hR : 0≤R)
      (_hs : Function.support f⊆Icc (-R) R),
      Commute U (Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f hf hc)))
    (t : ℝ) : Commute U (Wave.shiftedQuotientWave N t) := by
  have hpoint (v : AutomorphicSpace N) (t : ℝ) :
      U (Wave.shiftedQuotientWave N t v)=Wave.shiftedQuotientWave N t (U v) := by
    let u := fun t => U (Wave.shiftedQuotientWave N t v)-Wave.shiftedQuotientWave N t (U v)
    have hu : Continuous u := (U.continuous.comp (Wave.shiftedQuotientWave_stronglyContinuous N v)).sub
      (Wave.shiftedQuotientWave_stronglyContinuous N (U v))
    have hue : Function.Even u := fun s => by simp only [u,Wave.shiftedQuotientWave_neg]
    apply sub_eq_zero.mp
    apply continuous_even_eq_zero_of_even_tests u hu hue _ t
    intro g hg hc hge
    have hfc : HasCompactSupport (fun s => (g s:ℂ)) := hc.comp_left (g:=Complex.ofReal) (by simp)
    have hfs : ContDiff ℝ ∞ (fun s => (g s:ℂ)) := Complex.ofRealCLM.contDiff.comp hg
    let f : SchwartzMap ℝ ℂ := hfc.toSchwartzMap hfs
    have hfe : Function.Even f := fun s => by change (g (-s):ℂ)=(g s:ℂ);rw [hge]
    have hfr : ∀ s,star (f s)=f s := fun s => by change star (g s:ℂ)=(g s:ℂ);simp
    obtain ⟨R,hR,hRs⟩ := hfc.isCompact.isBounded.subset_closedBall_lt 0 (0:ℝ)
    have hs : Function.support f⊆Icc (-R) R := by
      intro s hsf
      have hb := hRs (subset_tsupport _ hsf)
      apply abs_le.mp
      simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero] using hb
    have hcomm := hU f (f.smooth ⊤) hfe hfc hfr R hR.le hs
    have hh : U (Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f (f.smooth ⊤) hfc) v)=
        Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f (f.smooth ⊤) hfc) (U v) :=
      DFunLike.congr_fun hcomm v
    have hi : Integrable (fun s => (g s:ℂ) • Wave.shiftedQuotientWave N s v) :=
      Wave.shiftedQuotientWave_packet_integrable N (compactSmoothWaveWeight _ hfs hfc) v
    have hj : Integrable (fun s => (g s:ℂ) • Wave.shiftedQuotientWave N s (U v)) :=
      Wave.shiftedQuotientWave_packet_integrable N (compactSmoothWaveWeight _ hfs hfc) (U v)
    have hiU : Integrable (fun s => (g s:ℂ) • U (Wave.shiftedQuotientWave N s v)) := by
      simpa only [Function.comp_def,map_smul] using U.integrable_comp hi
    have hmap : (∫ s,(g s:ℂ) • U (Wave.shiftedQuotientWave N s v))=
        U (∫ s,(g s:ℂ) • Wave.shiftedQuotientWave N s v) := by
      rw [← U.integral_comp_comm hi]
      simp only [map_smul]
    have hsub : (∫ s,g s • u s)=
        U (Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f (f.smooth ⊤) hfc) v)-
        Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f (f.smooth ⊤) hfc) (U v) := by
      change (∫ s,g s • u s)=
        U (∫ s,(g s:ℂ) • Wave.shiftedQuotientWave N s v)-
          ∫ s,(g s:ℂ) • Wave.shiftedQuotientWave N s (U v)
      have heq (s : ℝ) : g s • u s=
          (g s:ℂ) • U (Wave.shiftedQuotientWave N s v)-
            (g s:ℂ) • Wave.shiftedQuotientWave N s (U v) := by
        calc
          _ = (g s:ℂ) • u s := RCLike.real_smul_eq_coe_smul (K:=ℂ) (g s) (u s)
          _ = _ := smul_sub _ _ _
      simp_rw [heq]
      rw [integral_sub hiU hj,hmap]
    rw [hsub,hh,sub_self]
  apply ContinuousLinearMap.ext
  exact fun v => hpoint v t

#print axioms timePacket_commuting_wave

end QuantitativeMaass
