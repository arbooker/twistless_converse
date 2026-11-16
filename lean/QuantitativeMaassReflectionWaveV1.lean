module

public import QuantitativeMaassReflectionHeckeV1
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff SchwartzMap

namespace QuantitativeMaass

/-- Compact even smooth real tests separate continuous even vector functions.
Symmetrization reduces this to the fundamental lemma for arbitrary real tests. -/
theorem continuous_even_eq_zero_of_even_tests {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [CompleteSpace H] (u : ℝ → H) (hu : Continuous u)
    (he : Function.Even u)
    (hz : ∀ g : ℝ → ℝ,ContDiff ℝ ∞ g → HasCompactSupport g → Function.Even g →
      (∫ t,g t • u t)=0) : ∀ t,u t=0 := by
  have hae : u=ᵐ[volume](fun _ => 0) :=
    ae_eq_zero_of_integral_contDiff_smul_eq_zero hu.locallyIntegrable (by
      intro g hg hc
      have hgc : HasCompactSupport (fun t : ℝ => g (-t)) := hc.comp_homeomorph (Homeomorph.neg ℝ)
      have hgneg : ContDiff ℝ ∞ (fun t : ℝ => g (-t)) := hg.comp contDiff_id.neg
      have hi : Integrable (fun t => g t • u t) (volume : Measure ℝ) := (hg.continuous.smul hu).integrable_of_hasCompactSupport hc.smul_right
      have hin : Integrable (fun t => g (-t) • u t) (volume : Measure ℝ) := (hgneg.continuous.smul hu).integrable_of_hasCompactSupport hgc.smul_right
      have hs := hz (fun t => g t+g (-t)) (hg.add hgneg) (hc.add hgc)
        (fun t => by simp only [neg_neg,add_comm])
      have hneg : (∫ t,g (-t) • u t)=∫ t,g t • u t := by
        calc
          _ = ∫ t,g (-t) • u (-t) := by
            apply integral_congr_ae
            exact Eventually.of_forall (fun t => by change g (-t) • u t=g (-t) • u (-t); rw [he t])
          _ = _ := integral_neg_eq_self (fun t => g t • u t) volume
      simp_rw [add_smul] at hs
      rw [integral_add hi hin,hneg] at hs
      have htwo : (2:ℝ) • (∫ t,g t • u t)=0 := by simpa only [two_smul ℝ] using hs
      exact (smul_eq_zero.mp htwo).resolve_left (by norm_num))
  exact fun t => congrFun (Measure.eq_of_ae_eq hae hu continuous_const) t

/-- The actual reflection commutes with the unsmoothed shifted quotient wave.
The proof separates continuous even wave orbits using the already proved
commutation of genuine compact real even packets. -/
theorem reflectionIsometry_wave_commute (N : ℕ) [NeZero N] (t : ℝ) :
    Commute (reflectionIsometry N).toContinuousLinearMap (Wave.shiftedQuotientWave N t) := by
  let U := (reflectionIsometry N).toContinuousLinearMap
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
    have hcomm := evenWavePacket_reflection_commute N f hfc hfe hfr R hR.le hs
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

/-- Reflection commutes with the genuine LV difference, using actual Hecke
and unsmoothed wave commutation. -/
theorem reflectionIsometry_lvDifference_commute (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (A B : ℤ) (hAB : (p:ℤ)*A+(N:ℤ)*B=1) :
    Commute (reflectionIsometry N).toContinuousLinearMap (lvDifference N p hN hpN A B hAB) := by
  have hT := reflectionIsometry_hecke_commute N p hN hpN hNp A B hAB
  have hW := reflectionIsometry_wave_commute N (Real.log p)
  apply ContinuousLinearMap.ext
  intro v
  change (reflectionIsometry N).toContinuousLinearMap
    (HeckeL2.operator N p hN hpN A B hAB v - (2:ℂ) • Wave.shiftedQuotientWave N (Real.log p) v)=
      HeckeL2.operator N p hN hpN A B hAB (reflectionIsometry N v)-
        (2:ℂ) • Wave.shiftedQuotientWave N (Real.log p) (reflectionIsometry N v)
  have ht : (reflectionIsometry N).toContinuousLinearMap
      (HeckeL2.operator N p hN hpN A B hAB v)=
      HeckeL2.operator N p hN hpN A B hAB (reflectionIsometry N v) := DFunLike.congr_fun hT v
  have hw : (reflectionIsometry N).toContinuousLinearMap
      (Wave.shiftedQuotientWave N (Real.log p) v)=
      Wave.shiftedQuotientWave N (Real.log p) (reflectionIsometry N v) := DFunLike.congr_fun hW v
  rw [map_sub,map_smul,ht,hw]

/-- Every actual LV polynomial preserves reflection parity. -/
theorem reflectionIsometry_actualLVFilter_commute (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (A B : ℤ) (hAB : (p:ℤ)*A+(N:ℤ)*B=1) (d : ℕ) :
    Commute (reflectionIsometry N).toContinuousLinearMap (actualLVFilter N p hN hpN A B hAB d) := by
  let U := (reflectionIsometry N).toContinuousLinearMap
  let D := lvDifference N p hN hpN A B hAB
  let c : ℝ := ((lvBound p)^2)⁻¹
  let S : AutomorphicSpace N →L[ℂ] AutomorphicSpace N := 1-c • D^2
  have hD : Commute U D := reflectionIsometry_lvDifference_commute N p hN hpN hNp A B hAB
  have hDv (v : AutomorphicSpace N) : U (D v)=D (U v) := DFunLike.congr_fun hD v
  have hDD (v : AutomorphicSpace N) : U (D (D v))=D (D (U v)) := by
    rw [hDv,hDv]
  have hS : Commute U S := by
    apply ContinuousLinearMap.ext
    intro v
    change U (v-c • D (D v))=U v-c • D (D (U v))
    rw [map_sub,U.map_smul_of_tower,hDD]
  have hpow := hS.pow_right d
  apply ContinuousLinearMap.ext
  intro v
  change U (v-(S^d) v)=U v-(S^d) (U v)
  have hh : U ((S^d) v)=(S^d) (U v) := DFunLike.congr_fun hpow v
  rw [map_sub,hh]

#print axioms continuous_even_eq_zero_of_even_tests
#print axioms reflectionIsometry_wave_commute
#print axioms reflectionIsometry_lvDifference_commute
#print axioms reflectionIsometry_actualLVFilter_commute

end QuantitativeMaass
