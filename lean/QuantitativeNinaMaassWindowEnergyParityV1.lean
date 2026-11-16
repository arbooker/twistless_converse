module

public import QuantitativeNinaMaassNewParityV1
public import QuantitativeNinaMaassWindowEnergyUpperV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory QuantitativeMaass AsymptoticClassicalPetersson
open scoped Topology InnerProductSpace FourierTransform SchwartzMap ENNReal

namespace QuantitativeNinaMaass

local instance (N : ℕ) (hN : 0 < N) : NormedAddCommGroup (localCuspidalSpace N hN) :=
  inferInstance
local instance (N : ℕ) (hN : 0 < N) : InnerProductSpace ℂ (localCuspidalSpace N hN) :=
  inferInstance

def principalPacketEnergy {N : ℕ} {hN : 0 < N} (S : CuspEnergySpectrum N hN)
    (w : S.Index → ℝ) (f : SchwartzMap ℝ ℂ) : ℝ :=
  ∑' i : {i // 1 / 4 ≤ S.energy i}, ‖smoothPacketMultiplier f (S.energy i.val)‖ ^ 2 * w i.val

def cuspParityBasisWeight {N : ℕ} {hN : 0 < N} (S : CuspEnergySpectrum N hN)
    (η : ℝ) (i : S.Index) : ℝ :=
  ‖parityProjection N η (S.basis i : AutomorphicSpace N)‖ ^ 2

theorem cuspParityBasisWeight_add {N : ℕ} {hN : 0 < N} (S : CuspEnergySpectrum N hN)
    (η : ℝ) (hη : η ^ 2 = 1) (i : S.Index) :
    cuspParityBasisWeight S η i + cuspParityBasisWeight S (-η) i = 1 := by
  have hneg : (-η) ^ 2 = 1 := by simpa only [neg_sq] using hη
  have hh : ((cuspParityBasisWeight S η i + cuspParityBasisWeight S (-η) i : ℝ) : ℂ) =
      inner ℂ (S.basis i : AutomorphicSpace N) (S.basis i : AutomorphicSpace N) := by
    push_cast
    rw [cuspParityBasisWeight, cuspParityBasisWeight,
      parityProjection_energy N η hη, parityProjection_energy N (-η) hneg, Complex.ofReal_neg]
    ring
  have hre := congrArg Complex.re hh
  have hn : ‖(S.basis i : AutomorphicSpace N)‖ = 1 := S.basis.orthonormal.norm_eq_one i
  have hself : (inner ℂ (S.basis i : AutomorphicSpace N) (S.basis i : AutomorphicSpace N)).re =
      ‖(S.basis i : AutomorphicSpace N)‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  simpa only [Complex.ofReal_re, hself, hn, one_pow] using hre

theorem cuspParityBasisWeight_bounds {N : ℕ} {hN : 0 < N} (S : CuspEnergySpectrum N hN)
    (η : ℝ) (hη : η ^ 2 = 1) (i : S.Index) :
    cuspParityBasisWeight S η i ∈ Icc (0 : ℝ) 1 := by
  have hh := cuspParityBasisWeight_add S η hη i
  have hp : 0 ≤ cuspParityBasisWeight S η i := sq_nonneg _
  have hn : 0 ≤ cuspParityBasisWeight S (-η) i := sq_nonneg _
  exact ⟨hp, by linarith⟩

theorem cuspPacket_scalar_summable {N : ℕ} {hN : 0 < N} (S : CuspEnergySpectrum N hN)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ)) :
    Summable (fun i => ‖smoothPacketMultiplier f (S.energy i)‖ ^ 2) := by
  have ho : Orthonormal ℂ (fun i => (S.basis i : AutomorphicSpace N)) :=
    S.basis.orthonormal.comp_linearIsometry (localCuspidalSpace N hN).subtypeₗᵢ
  have hh := cuspidal_smooth_packet_square_summable N hN _ ho
    (fun i => (S.basis i).property) S.energy S.energy_nonneg S.graph f (f.smooth ⊤) hc
  apply hh.congr
  intro i
  rw [Wave.shiftedQuotientWavePacket_eigen N f _ (S.energy_nonneg i) (S.graph i),
    norm_smul, ho.norm_eq_one i, mul_one]
  rfl

theorem principalPacketEnergy_summable {N : ℕ} {hN : 0 < N} (S : CuspEnergySpectrum N hN)
    (w : S.Index → ℝ) (hw : ∀ i, w i ∈ Icc (0 : ℝ) 1)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ)) :
    Summable (fun i : {i // 1 / 4 ≤ S.energy i} =>
      ‖smoothPacketMultiplier f (S.energy i.val)‖ ^ 2 * w i.val) := by
  exact Summable.of_nonneg_of_le
    (fun i : {i // 1 / 4 ≤ S.energy i} =>
      mul_nonneg (sq_nonneg ‖smoothPacketMultiplier f (S.energy i.val)‖) (hw i.val).1)
    (fun i : {i // 1 / 4 ≤ S.energy i} =>
      mul_le_of_le_one_right (sq_nonneg ‖smoothPacketMultiplier f (S.energy i.val)‖) (hw i.val).2)
    ((cuspPacket_scalar_summable S f hc).subtype _)

/-- A literal window is bounded by its actual principal packet energy
whenever the cosine multiplier majorizes one on that window. -/
theorem principalPacketEnergy_window_le {N : ℕ} {hN : 0 < N} (S : CuspEnergySpectrum N hN)
    (w : S.Index → ℝ) (hw : ∀ i, w i ∈ Icc (0 : ℝ) 1)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ)) (a b : ℝ)
    (hmajor : ∀ r ∈ Icc a b, 1 ≤ ‖cosinePacket f r‖ ^ 2) :
    principalWindowWeight S.energy w a b ≤ principalPacketEnergy S w f := by
  let J := principalWindowIndices S.energy a b
  have ho : Orthonormal ℂ (fun i => (S.basis i : AutomorphicSpace N)) :=
    S.basis.orthonormal.comp_linearIsometry (localCuspidalSpace N hN).subtypeₗᵢ
  let : Fintype J := (principalWindowIndices_finite N hN _ ho (fun i => (S.basis i).property)
    S.energy S.energy_nonneg S.graph a b).fintype
  let inc : J → {i // 1 / 4 ≤ S.energy i} := fun i => ⟨i.val, i.property.1⟩
  have hi : Function.Injective inc := by
    intro i j hij
    apply Subtype.ext
    exact congrArg (fun x : {i // 1 / 4 ≤ S.energy i} => x.val) hij
  have hs := principalPacketEnergy_summable S w hw f hc
  have hpoint (i : J) : w i.val ≤ ‖smoothPacketMultiplier f (S.energy i.val)‖ ^ 2 * w i.val := by
    have heq : S.energy i.val = 1 / 4 + (Real.sqrt (S.energy i.val - 1 / 4)) ^ 2 := by
      rw [Real.sq_sqrt (sub_nonneg.mpr i.property.1)]
      ring
    have hm : 1 ≤ ‖smoothPacketMultiplier f (S.energy i.val)‖ ^ 2 := by
      rw [heq, smoothPacketMultiplier_principal]
      exact hmajor _ i.property.2
    exact le_mul_of_one_le_left (hw i.val).1 hm
  calc
    _ ≤ ∑' i : J, ‖smoothPacketMultiplier f (S.energy i.val)‖ ^ 2 * w i.val :=
      Summable.tsum_le_tsum hpoint Summable.of_finite Summable.of_finite
    _ ≤ _ := Summable.tsum_le_tsum_of_inj inc hi
      (fun i _ => mul_nonneg (sq_nonneg _) (hw i.val).1) (fun _ => le_rfl)
      Summable.of_finite hs

/-- Exact parity splitting on the principal spectrum is bounded by the
whole actual cuspidal packet energy, retaining exceptional energies. -/
theorem principalParityPacketEnergy_add_le {N : ℕ} {hN : 0 < N} (S : CuspEnergySpectrum N hN)
    (η : ℝ) (hη : η ^ 2 = 1) (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ → ℂ)) :
    principalPacketEnergy S (cuspParityBasisWeight S η) f +
      principalPacketEnergy S (cuspParityBasisWeight S (-η)) f ≤
        ∑' i, ‖Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f (f.smooth ⊤) hc)
          (S.basis i : AutomorphicSpace N)‖ ^ 2 := by
  have hneg : (-η) ^ 2 = 1 := by simpa only [neg_sq] using hη
  have hp := principalPacketEnergy_summable S _ (cuspParityBasisWeight_bounds S η hη) f hc
  have hn := principalPacketEnergy_summable S _ (cuspParityBasisWeight_bounds S (-η) hneg) f hc
  have hscalar (i : S.Index) :
      ‖Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f (f.smooth ⊤) hc)
        (S.basis i : AutomorphicSpace N)‖ ^ 2 = ‖smoothPacketMultiplier f (S.energy i)‖ ^ 2 := by
    have hi : ‖(S.basis i : AutomorphicSpace N)‖ = 1 := S.basis.orthonormal.norm_eq_one i
    rw [Wave.shiftedQuotientWavePacket_eigen N f _ (S.energy_nonneg i) (S.graph i),
      norm_smul, hi, mul_one]
    rfl
  simp only [principalPacketEnergy, hscalar]
  rw [← hp.tsum_add hn]
  simp_rw [← mul_add, cuspParityBasisWeight_add S η hη, mul_one]
  exact tsum_comp_le_tsum_of_inj (cuspPacket_scalar_summable S f hc) (fun _ => sq_nonneg _)
    Subtype.val_injective

theorem originalWindowMajorant_norm_majorizes (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x : ℂ))))
    (hK : ∀ x, 0 ≤ K x) (hm : (∫ x, K x) = 1)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop, 0 < ε t ∧ ε t ≤ 1)
    (hproduct : Tendsto (fun t => ε t * slowScale t) atTop atTop) :
    ∀ᶠ t in atTop, ∀ r ∈ Icc t (t + ε t), 1 ≤ ‖cosinePacket (originalWindowMajorant K hc ε t) r‖ ^ 2 := by
  filter_upwards [originalWindowMajorant_majorizes K he hc hK hm ε hε hproduct] with t ht
  intro r hr
  have hp := (ht r hr).trans (Complex.re_le_norm _)
  nlinarith [norm_nonneg (cosinePacket (originalWindowMajorant K hc ε t) r)]

/-- The fixed-parity principal packet has the sharp full-cusp coefficient
at the original schedule. Its upper bound follows from the other parity's
sharp lower bound and the whole-cusp geometric upper trace. -/
theorem originalWindowMajorant_principal_parity_limit {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (η : ℝ) (hη : η ^ 2 = 1)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x : ℂ))))
    (hK : ∀ x, 0 ≤ K x) (hm : (∫ x, K x) = 1)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop, 0 < ε t ∧ ε t ≤ 1)
    (hproduct : Tendsto (fun t => ε t * slowScale t) atTop atTop) :
    Tendsto (fun t => principalPacketEnergy S (cuspParityBasisWeight S η)
      (originalWindowMajorant K hc ε t) / (t * ε t))
      atTop (𝓝 ((quotientMeasure N).real univ / (4 * Real.pi))) := by
  have hneg : (-η) ^ 2 = 1 := by simpa only [neg_sq] using hη
  let C := fun σ t => principalWindowWeight S.energy (cuspParityBasisWeight S σ) t (t + ε t) /
    (t * ε t)
  have hC (σ : ℝ) (hσ : σ ^ 2 = 1) :
      Tendsto (C σ) atTop (𝓝 ((quotientMeasure N).real univ / (4 * Real.pi))) := by
    have hEq (t : ℝ) : principalWindowWeight S.energy (cuspParityBasisWeight S σ) t (t + ε t) =
        (Module.finrank ℂ (S.parityBand t (t + ε t) σ) : ℝ) :=
      sharp_parity_weight_eq_dimension N hN S.basis S.energy S.energy_nonneg S.graph _ _ σ hσ
    unfold C
    simp_rw [hEq]
    exact S.parityBand_short_weyl σ hσ ε hε hproduct
  have ho : Orthonormal ℂ (fun i => (S.basis i : AutomorphicSpace N)) :=
    S.basis.orthonormal.comp_linearIsometry (localCuspidalSpace N hN).subtypeₗᵢ
  obtain ⟨U, hU, hu⟩ := originalWindowMajorant_cuspidal_upper_limit N hN K he hc hK hm
    _ ho (fun i => (S.basis i).property) ε hε hproduct
  have hupper : Tendsto (fun t => U t - C (-η) t) atTop
      (𝓝 ((quotientMeasure N).real univ / (4 * Real.pi))) := by
    convert hU.sub (hC (-η) hneg) using 1
    congr 1
    ring
  have hlower (σ : ℝ) (hσ : σ ^ 2 = 1) :
      ∀ᶠ t in atTop, C σ t ≤ principalPacketEnergy S (cuspParityBasisWeight S σ)
        (originalWindowMajorant K hc ε t) / (t * ε t) := by
    filter_upwards [originalWindowMajorant_norm_majorizes K he hc hK hm ε hε hproduct,
      hε, eventually_gt_atTop (0 : ℝ)] with t ht het ht0
    exact div_le_div_of_nonneg_right
      (principalPacketEnergy_window_le S _ (cuspParityBasisWeight_bounds S σ hσ)
        _ (originalWindowMajorant_compact K hc ε t) _ _ ht) (mul_pos ht0 het.1).le
  apply (hC η hη).squeeze' hupper (hlower η hη)
  filter_upwards [hu, hlower (-η) hneg, hε, eventually_gt_atTop (0 : ℝ)] with t hut hlt het ht0
  have hadd := div_le_div_of_nonneg_right
    (principalParityPacketEnergy_add_le S η hη _ (originalWindowMajorant_compact K hc ε t))
    (mul_pos ht0 het.1).le
  rw [add_div] at hadd
  linarith

#print axioms cuspParityBasisWeight_add
#print axioms cuspParityBasisWeight_bounds
#print axioms cuspPacket_scalar_summable
#print axioms principalPacketEnergy_summable
#print axioms principalPacketEnergy_window_le
#print axioms principalParityPacketEnergy_add_le
#print axioms originalWindowMajorant_norm_majorizes
#print axioms originalWindowMajorant_principal_parity_limit

end QuantitativeNinaMaass
