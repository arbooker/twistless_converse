module

public import QuantitativeNinaMaassNewParityEnergyLimitV1
public import QuantitativeMaassPositiveWindowKernelV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory QuantitativeMaass AsymptoticClassicalPetersson
open scoped Topology InnerProductSpace FourierTransform SchwartzMap

namespace QuantitativeNinaMaass

/-- A weighted full sum differs from its restricted sum by at most the
unweighted omitted mass. All real subtractions occur after summability. -/
theorem weighted_tsum_subtype_sandwich {ι : Type*} (q w : ι → ℝ)
    (hq : Summable q) (hq0 : ∀ i, 0 ≤ q i) (hw : ∀ i, w i ∈ Icc (0 : ℝ) 1) (P : Set ι) :
    (∑' i : P, q i.val * w i.val) ≤ ∑' i, q i * w i ∧
      (∑' i, q i * w i) ≤ (∑' i : P, q i.val * w i.val) +
        (∑' i, q i) - ∑' i : P, q i.val := by
  have hwq : Summable (fun i => q i * w i) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hq0 i) (hw i).1)
      (fun i => mul_le_of_le_one_right (hq0 i) (hw i).2) hq
  have hl := tsum_comp_le_tsum_of_inj hwq (fun i => mul_nonneg (hq0 i) (hw i).1)
    (show Function.Injective (fun i : P => i.val) from Subtype.val_injective)
  have hd := tsum_comp_le_tsum_of_inj (hq.sub hwq)
    (fun i => sub_nonneg.mpr (mul_le_of_le_one_right (hq0 i) (hw i).2))
    (show Function.Injective (fun i : P => i.val) from Subtype.val_injective)
  change (∑' i : P, (q i.val - q i.val * w i.val)) ≤ ∑' i, (q i - q i * w i) at hd
  have hqp : Summable (fun i : P => q i.val) := hq.subtype P
  have hwqp : Summable (fun i : P => q i.val * w i.val) := hwq.subtype P
  rw [hqp.tsum_sub hwqp, hq.tsum_sub hwq] at hd
  exact ⟨hl, by linarith⟩

local instance (N : ℕ) (hN : 0 < N) : NormedAddCommGroup (localCuspidalSpace N hN) :=
  inferInstance
local instance (N : ℕ) (hN : 0 < N) : InnerProductSpace ℂ (localCuspidalSpace N hN) :=
  inferInstance

theorem principalParityPacketEnergy_add {N : ℕ} {hN : 0 < N} (S : CuspEnergySpectrum N hN)
    (η : ℝ) (hη : η ^ 2 = 1) (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ → ℂ)) :
    principalPacketEnergy S (cuspParityBasisWeight S η) f +
      principalPacketEnergy S (cuspParityBasisWeight S (-η)) f =
        principalPacketEnergy S (fun _ => 1) f := by
  have hneg : (-η) ^ 2 = 1 := by simpa only [neg_sq] using hη
  have hp := principalPacketEnergy_summable S _ (cuspParityBasisWeight_bounds S η hη) f hc
  have hn := principalPacketEnergy_summable S _ (cuspParityBasisWeight_bounds S (-η) hneg) f hc
  unfold principalPacketEnergy
  rw [← hp.tsum_add hn]
  simp_rw [← mul_add, cuspParityBasisWeight_add S η hη]

/-- A fixed support multiplier chosen from the actual kernel, independent
of center and width. -/
def originalWindowPropagationConstant (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x : ℂ)))) : ℝ :=
  (originalWindowMajorant_support K hc).choose

theorem originalWindowPropagationConstant_pos (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x : ℂ)))) :
    0 < originalWindowPropagationConstant K hc :=
  (originalWindowMajorant_support K hc).choose_spec.1

theorem originalWindowPropagationConstant_support (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x : ℂ)))) (ε : ℝ → ℝ) (t : ℝ) :
    Function.support (originalWindowMajorant K hc ε t) ⊆
      Icc (-(originalWindowPropagationConstant K hc * positiveWindowRadius ε t))
        (originalWindowPropagationConstant K hc * positiveWindowRadius ε t) :=
  (originalWindowMajorant_support K hc).choose_spec.2 ε t

/-- The genuine completed-new-parity operator used by the original-window
majorant, with every compactness and propagation premise proved. -/
def originalNewParityWindowPacket (N : ℕ) [NeZero N] (hN : 0 < N) (η : ℝ)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x : ℂ)))) (ε : ℝ → ℝ) (t : ℝ) :
    completedCuspidalNewParitySpace N hN η →L[ℂ] completedCuspidalNewParitySpace N hN η :=
  completedCuspidalNewParityTimePacket N hN η (originalWindowMajorant K hc ε t)
    (originalWindowMajorant_compact K hc ε t) (originalWindowMajorant_even K he hc ε t)
    (originalWindowMajorant_real K he hc ε t)
    (originalWindowPropagationConstant K hc * positiveWindowRadius ε t)
    (mul_pos (originalWindowPropagationConstant_pos K hc) (positiveWindowRadius_pos ε t)).le
    (originalWindowPropagationConstant_support K hc ε t)

/-- Sharp actual completed-new-parity packet energy at every admissible
level. The exceptional mass is squeezed out by the whole-cusp upper bound
and the two principal parity limits, with no stronger shrinking condition. -/
theorem originalNewParityWindowPacket_energy_limit {ι : Type*}
    (N : ℕ) [NeZero N] (hN : GridAdmissibleGap.Admissible N) (η : ℝ) (hη : η ^ 2 = 1)
    (b : HilbertBasis ι ℂ (completedCuspidalNewParitySpace N hN.1 η))
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x : ℂ))))
    (hK : ∀ x, 0 ≤ K x) (hm : (∫ x, K x) = 1)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop, 0 < ε t ∧ ε t ≤ 1)
    (hproduct : Tendsto (fun t => ε t * slowScale t) atTop atTop) :
    Tendsto (fun t => hilbertSchmidtEnergy b
      (originalNewParityWindowPacket N hN.1 η K he hc ε t) / (t * ε t))
      atTop (𝓝 (AsymptoticTotalNewCorner.arithmeticCoefficient N)) := by
  let S := geometricCuspSpectrum N hN.1
  let f := originalWindowMajorant K hc ε
  let P := fun t => principalPacketEnergy S (newParitySpectralWeight S η) (f t) / (t * ε t)
  let Q := fun t => principalPacketEnergy S (fun _ => 1) (f t) / (t * ε t)
  have hP : Tendsto P atTop (𝓝 (AsymptoticTotalNewCorner.arithmeticCoefficient N)) := by
    simpa only [packetParityEnergy_univ N hN.1 η hη _ (originalWindowMajorant_compact K hc ε _)]
      using originalPacketParityEnergy_univ_limit N hN η hη K he hc hK hm ε hε hproduct
  have hQ : Tendsto Q atTop (𝓝 ((quotientMeasure N).real univ / (2 * Real.pi))) := by
    have hp := originalWindowMajorant_principal_parity_limit S η hη K he hc hK hm ε hε hproduct
    have hn := originalWindowMajorant_principal_parity_limit S (-η)
      (by simpa only [neg_sq] using hη) K he hc hK hm ε hε hproduct
    have heq (t : ℝ) : Q t =
        principalPacketEnergy S (cuspParityBasisWeight S η) (f t) / (t * ε t) +
          principalPacketEnergy S (cuspParityBasisWeight S (-η)) (f t) / (t * ε t) := by
      rw [← add_div, principalParityPacketEnergy_add S η hη _ (originalWindowMajorant_compact K hc ε t)]
    convert hp.add hn using 1
    · funext t
      exact heq t
    · congr 1
      ring
  have ho : Orthonormal ℂ (fun i => (S.basis i : AutomorphicSpace N)) :=
    S.basis.orthonormal.comp_linearIsometry (localCuspidalSpace N hN.1).subtypeₗᵢ
  obtain ⟨U, hU, hu⟩ := originalWindowMajorant_cuspidal_upper_limit N hN.1 K he hc hK hm
    _ ho (fun i => (S.basis i).property) ε hε hproduct
  have hupper : Tendsto (fun t => P t + U t - Q t) atTop
      (𝓝 (AsymptoticTotalNewCorner.arithmeticCoefficient N)) := by
    simpa only [add_sub_cancel_right] using (hP.add hU).sub hQ
  have hbounds : ∀ᶠ t in atTop,
      P t ≤ hilbertSchmidtEnergy b (originalNewParityWindowPacket N hN.1 η K he hc ε t) / (t * ε t) ∧
        hilbertSchmidtEnergy b (originalNewParityWindowPacket N hN.1 η K he hc ε t) / (t * ε t) ≤
          P t + U t - Q t := by
    filter_upwards [hu, hε, eventually_gt_atTop (0 : ℝ)] with t hut het ht0
    have hh := weighted_tsum_subtype_sandwich
      (fun i => ‖smoothPacketMultiplier (f t) (S.energy i)‖ ^ 2) (newParitySpectralWeight S η)
      (cuspPacket_scalar_summable S _ (originalWindowMajorant_compact K hc ε t))
      (fun _ => sq_nonneg _) (newParitySpectralWeight_bounds S η) {i | 1 / 4 ≤ S.energy i}
    have he := (newParityPacket_spectral_energy S η b (f t)
      (originalWindowMajorant_compact K hc ε t) (originalWindowMajorant_even K he hc ε t)
      (originalWindowMajorant_real K he hc ε t)
      (originalWindowPropagationConstant K hc * positiveWindowRadius ε t)
      (mul_pos (originalWindowPropagationConstant_pos K hc) (positiveWindowRadius_pos ε t)).le
      (originalWindowPropagationConstant_support K hc ε t)).tsum_eq
    have hscalar (i : S.Index) :
        ‖Wave.shiftedQuotientWavePacket N (f t) (compactSmoothWaveWeight _ ((f t).smooth ⊤)
          (originalWindowMajorant_compact K hc ε t)) (S.basis i : AutomorphicSpace N)‖ ^ 2 =
            ‖smoothPacketMultiplier (f t) (S.energy i)‖ ^ 2 := by
      rw [Wave.shiftedQuotientWavePacket_eigen N _ _ (S.energy_nonneg i) (S.graph i),
        norm_smul, ho.norm_eq_one i, mul_one]
      rfl
    have hut' : (∑' i, ‖smoothPacketMultiplier (f t) (S.energy i)‖ ^ 2) /
        (t * ε t) ≤ U t := by
      calc
        _ = (∑' i, ‖Wave.shiftedQuotientWavePacket N (f t)
            (compactSmoothWaveWeight _ ((f t).smooth ⊤)
              (originalWindowMajorant_compact K hc ε t))
            (S.basis i : AutomorphicSpace N)‖ ^ 2) / (t * ε t) :=
          congrArg (fun x : ℝ => x / (t * ε t)) (tsum_congr (fun i => (hscalar i).symm))
        _ ≤ U t := hut
    rw [he] at hh
    have hlo := div_le_div_of_nonneg_right hh.1 (mul_pos ht0 het.1).le
    have hhi := div_le_div_of_nonneg_right hh.2 (mul_pos ht0 het.1).le
    simp only [sub_div, add_div] at hhi
    change P t ≤ _ at hlo
    refine ⟨hlo, ?_⟩
    have hQid : Q t = (∑' i : {i // 1 / 4 ≤ S.energy i},
        ‖smoothPacketMultiplier (f t) (S.energy i.val)‖ ^ 2) / (t * ε t) := by
      simp only [Q, principalPacketEnergy, mul_one]
    rw [hQid]
    exact hhi.trans (sub_le_sub_right (add_le_add (le_refl (P t)) hut') _)
  exact hP.squeeze' hupper (hbounds.mono (fun _ h => h.1)) (hbounds.mono (fun _ h => h.2))

/-- Direct input package for the original-count sandwich: actual real even
compact smooth majorants, a fixed multiple of the original propagation
radius, and the sharp completed-new-parity energy. The kernel is constructed
internally; only the manuscript level, parity and width hypotheses remain. -/
theorem exists_original_newParity_energy_majorants {ι : Type*}
    (N : ℕ) [NeZero N] (hN : GridAdmissibleGap.Admissible N) (η : ℝ) (hη : η ^ 2 = 1)
    (b : HilbertBasis ι ℂ (completedCuspidalNewParitySpace N hN.1 η))
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop, 0 < ε t ∧ ε t ≤ 1)
    (hproduct : Tendsto (fun t => ε t * slowScale t) atTop atTop) :
    ∃ (f : ℝ → SchwartzMap ℝ ℂ)
      (hc : ∀ t, HasCompactSupport (f t : ℝ → ℂ))
      (he : ∀ t, Function.Even (f t)) (hr : ∀ t s, star (f t s) = f t s)
      (B : ℝ) (hB : 0 < B)
      (hs : ∀ t, Function.support (f t) ⊆
        Icc (-(B * positiveWindowRadius ε t)) (B * positiveWindowRadius ε t)),
      (∀ᶠ t in atTop, ∀ r ∈ Icc t (t + ε t), 1 ≤ (cosinePacket (f t) r).re) ∧
      Tendsto (fun t => B * positiveWindowRadius ε t / slowScale t) atTop (𝓝 0) ∧
      Tendsto (fun t => hilbertSchmidtEnergy b
        (completedCuspidalNewParityTimePacket N hN.1 η (f t) (hc t) (he t) (hr t)
          (B * positiveWindowRadius ε t) (mul_pos hB (positiveWindowRadius_pos ε t)).le (hs t)) /
          (t * ε t)) atTop (𝓝 (AsymptoticTotalNewCorner.arithmeticCoefficient N)) := by
  obtain ⟨K, hK, he, hm, hc⟩ := exists_positive_bandlimited_window_kernel
  refine ⟨originalWindowMajorant K hc ε, originalWindowMajorant_compact K hc ε,
    originalWindowMajorant_even K he hc ε, originalWindowMajorant_real K he hc ε,
    originalWindowPropagationConstant K hc, originalWindowPropagationConstant_pos K hc,
    originalWindowPropagationConstant_support K hc ε,
    originalWindowMajorant_majorizes K he hc hK hm ε hε hproduct,
    originalWindowMajorant_radius_limit _ ε (hε.mono (fun _ h => h.1)) hproduct, ?_⟩
  exact originalNewParityWindowPacket_energy_limit N hN η hη b K he hc hK hm ε hε hproduct

#print axioms weighted_tsum_subtype_sandwich
#print axioms principalParityPacketEnergy_add
#print axioms originalWindowPropagationConstant_pos
#print axioms originalWindowPropagationConstant_support
#print axioms originalNewParityWindowPacket_energy_limit
#print axioms exists_original_newParity_energy_majorants

end QuantitativeNinaMaass
