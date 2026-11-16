module

public import QuantitativeArithmeticMaassMovingSectorFilterV1
public import QuantitativeArithmeticMaassScheduledTraceCompressionV1

set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory ContinuousLinearMap
open QuantitativeNinaMaass AsymptoticClassicalPetersson AsymptoticSectorSigns
open QuantitativeNewGap QuantitativeArithmeticRepeatedTwoBands QuantitativeArithmeticNewBandProjections
open QuantitativeArithmeticNewBandProduct
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled
local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    NormedAddCommGroup (S.parityBand a b σ) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    InnerProductSpace ℂ (S.parityBand a b σ) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    FiniteDimensional ℂ (S.parityBand a b σ) := by
  let := S.band_finiteDimensional a b
  infer_instance




local instance (N : ℕ) (p : ↥N.primeFactors) : NeZero p.val :=
  ⟨(Nat.prime_of_mem_primeFactors p.property).ne_zero⟩

local instance (N : ℕ) [NeZero N] (p : ↥N.primeFactors) : NeZero (N/p.val) :=
  ⟨(prime_quotient_pos N p.val (NeZero.pos N)
    (Nat.prime_of_mem_primeFactors p.property) (Nat.dvd_of_mem_primeFactors p.property)).ne'⟩

local instance {N : ℕ} [NeZero N] {hN : 0<N}
    (T : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    CompleteSpace (T.parityBand a b σ) := FiniteDimensional.complete ℂ _

local instance {N : ℕ} [NeZero N] {hN : 0<N}
    (T : CuspEnergySpectrum N hN) (a b σ : ℝ)
    (K : Submodule ℂ (T.parityBand a b σ)) : K.HasOrthogonalProjection := by
  let : CompleteSpace K := FiniteDimensional.complete ℂ _
  infer_instance



local instance {N : ℕ} [NeZero N] {hN : 0<N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (K : Submodule ℂ (S.parityBand a b σ)) :
    CompleteSpace K := FiniteDimensional.complete ℂ _



local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    FiniteDimensional ℂ (S.band a b) := S.band_finiteDimensional a b

variable (N : ℕ) [NeZero N] (hN : 0<N) (T : CuspEnergySpectrum N hN)
    (S : ∀ p : ↥N.primeFactors, CuspEnergySpectrum (N/p.val)
      (prime_quotient_pos N p.val hN (Nat.prime_of_mem_primeFactors p.property)
        (Nat.dvd_of_mem_primeFactors p.property))) (σ : ℝ) (e : Sector N)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)


/-- The actual moving-cutoff wave column in its finite parity band. -/
def movingParityColumn (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (he : Function.Even K)
    (ε : ℝ→ℝ) (B C D t : ℝ) :
    UpperHalfPlane→T.parityBand (t-Real.exp (B*Strong.strongScale t))
      (t+Real.exp (B*Strong.strongScale t)) σ :=
  fun z => (T.parityBand (t-Real.exp (B*Strong.strongScale t))
    (t+Real.exp (B*Strong.strongScale t)) σ).orthogonalProjectionOnto
    (WideInput.bandTransfer T t (Real.exp (B*Strong.strongScale t))
      (cutoffTransfer N (movingLowerEdge δ C ε t) D t (movingLowerEdge_pos hδ C ε t))
      (column K hc he ε t z))

theorem movingParityColumn_memLp (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (he : Function.Even K)
    (ε : ℝ→ℝ) (B C D t : ℝ) :
    MemLp (movingParityColumn N hN T σ hδ K hc he ε B C D t) 2 (quotientMeasure 0) := by
  exact (WideInput.bandTransfer_column_memLp T t (Real.exp (B*Strong.strongScale t)) _
    (column K hc he ε t) (movingCutoff_column_memLp N hδ C D K hc he ε t)).continuousLinearMap_comp _

theorem movingParityColumn_energy (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (he : Function.Even K)
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (B C D : ℝ) (hC : 0≤C) :
    ∀ᶠ t in atTop,(∫ z,‖movingParityColumn N hN T σ hδ K hc he ε B C D t z‖^2 ∂quotientMeasure 0)≤
      Real.exp (22*Strong.strongScale t)*(t*ε t) := by
  filter_upwards [movingCutoffTransfer_energy K hc he hK hm ε hε hp hδ C hC] with t ht
  apply le_trans _ (ht N D)
  have hx := movingParityColumn_memLp N hN T σ hδ K hc he ε B C D t
  have hy := movingCutoff_column_memLp N hδ C D K hc he ε t
  apply integral_mono ((memLp_two_iff_integrable_sq_norm hx.aestronglyMeasurable).mp hx)
    ((memLp_two_iff_integrable_sq_norm hy.aestronglyMeasurable).mp hy)
  intro z
  apply pow_le_pow_left₀ (norm_nonneg _)
  apply ((T.parityBand (t-Real.exp (B*Strong.strongScale t))
    (t+Real.exp (B*Strong.strongScale t)) σ).norm_orthogonalProjectionOnto_apply_le _).trans
  apply ((T.band (t-Real.exp (B*Strong.strongScale t))
    (t+Real.exp (B*Strong.strongScale t))).norm_orthogonalProjectionOnto_apply_le _).trans
  exact (localCuspidalSpace N hN).norm_orthogonalProjectionOnto_apply_le _

/-- The local-new/sign polynomial replaces the exact canonical sector in
the actual quadratic wave trace, with no loss of its leading coefficient. -/
theorem movingBand_canonicalSector_observed_trace_limit
    (hAd : GridAdmissibleGap.Admissible N) (B W C D : ℝ) (hB : 0≤B) (hC : 0≤C)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (V : (t : ℝ) → T.parityBand (t-Real.exp (B*Strong.strongScale t))
      (t+Real.exp (B*Strong.strongScale t)) σ→L[ℂ]
        T.parityBand (t-Real.exp (B*Strong.strongScale t)) (t+Real.exp (B*Strong.strongScale t)) σ)
    (hV : ∀ t,‖V t‖≤1) :
    Tendsto (fun t =>
      let a := t-Real.exp (B*Strong.strongScale t)
      let b := t+Real.exp (B*Strong.strongScale t)
      let c := movingParityColumn N hN T σ hδ K hc he ε B C D t
      let F := sectorParityBandFilter N hN T S a b σ e (growingLVDegree t)
      let P := (sectorParityBandSpace T a b σ e).starProjection
      Real.exp (W*Strong.strongScale t)*
        (columnLinearTrace (quotientMeasure 0) (fun z => F (c z)) (V t)-
         columnLinearTrace (quotientMeasure 0) (fun z => P (c z)) (V t))/(t*ε t)) atTop (𝓝 0) := by
  let c := fun t => movingParityColumn N hN T σ hδ K hc he ε B C D t
  let F := fun t => sectorParityBandFilter N hN T S (t-Real.exp (B*Strong.strongScale t))
    (t+Real.exp (B*Strong.strongScale t)) σ e (growingLVDegree t)
  let P := fun t => (sectorParityBandSpace T (t-Real.exp (B*Strong.strongScale t))
    (t+Real.exp (B*Strong.strongScale t)) σ e).starProjection
  let E := fun t => ∫ z,‖F t (c t z)-P t (c t z)‖^2 ∂quotientMeasure 0
  have hlim : Tendsto (fun t => Real.exp ((W+(|W|+22+1))*Strong.strongScale t)*E t/(t*ε t)) atTop (𝓝 0) := by
    simpa only [E,F,P,c,movingParityColumn,sub_apply] using
      movingBand_canonicalSector_energy_limit N hN T S σ e hδ hAd B (W+(|W|+22+1)) C D hB hC
        K hc he ε hε hp
  apply weighted_trace_from_energy ε E _ 1 22 W (by norm_num) (by norm_num)
    (hε.mono (fun _ h => h.1)) hp (Eventually.of_forall (fun _ => integral_nonneg (fun _ => sq_nonneg _))) hlim
  filter_upwards [movingParityColumn_energy N hN T σ hδ K hc he hK hm ε hε hp B C D hC,
    hε,eventually_gt_atTop (0:ℝ)] with t hmass heps ht
  have hcol := movingParityColumn_memLp N hN T σ hδ K hc he ε B C D t
  have hF := hcol.continuousLinearMap_comp (F t)
  have hP := hcol.continuousLinearMap_comp (P t)
  have hmassP : (∫ z,‖P t (c t z)‖^2 ∂quotientMeasure 0)≤Real.exp (22*Strong.strongScale t)*t := by
    apply le_trans _ ((mul_le_mul_of_nonneg_left (mul_le_of_le_one_right ht.le heps.2)
      (Real.exp_pos (22*Strong.strongScale t)).le))
    apply le_trans _ hmass
    apply integral_mono ((memLp_two_iff_integrable_sq_norm hP.aestronglyMeasurable).mp hP)
      ((memLp_two_iff_integrable_sq_norm hcol.aestronglyMeasurable).mp hcol)
    intro z
    exact pow_le_pow_left₀ (norm_nonneg _) (Submodule.norm_starProjection_apply_le _ _) 2
  let η := Real.exp (-((|W|+22+1)*Strong.strongScale t))
  have hh := columnLinearTrace_column_perturbation (quotientMeasure 0)
    (fun z => F t (c t z)) (fun z => P t (c t z)) hF hP (V t) η (Real.exp_pos _)
  have hn := hV t
  have hmain := hh.trans (mul_le_of_le_one_left
    (add_nonneg (mul_nonneg (Real.exp_pos _).le (integral_nonneg (fun _ => sq_nonneg _)))
      (mul_nonneg (by positivity) (integral_nonneg (fun _ => sq_nonneg _)))) hn)
  apply hmain.trans
  dsimp only [E]
  have hm' := mul_le_mul_of_nonneg_left hmassP (Real.exp_pos (-((|W|+22+1)*Strong.strongScale t))).le
  simpa only [one_mul,mul_comm t] using add_le_add hm' (le_refl ((1+η⁻¹)*E t))

/-- Identity observation of the canonical trace comparison. -/
theorem movingBand_canonicalSector_trace_limit
    (hAd : GridAdmissibleGap.Admissible N) (B W C D : ℝ) (hB : 0≤B) (hC : 0≤C)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t =>
      let a := t-Real.exp (B*Strong.strongScale t)
      let b := t+Real.exp (B*Strong.strongScale t)
      let c := movingParityColumn N hN T σ hδ K hc he ε B C D t
      let F := sectorParityBandFilter N hN T S a b σ e (growingLVDegree t)
      let P := (sectorParityBandSpace T a b σ e).starProjection
      Real.exp (W*Strong.strongScale t)*
        (columnLinearTrace (quotientMeasure 0) (fun z => F (c z)) 1-
         columnLinearTrace (quotientMeasure 0) (fun z => P (c z)) 1)/(t*ε t)) atTop (𝓝 0) := by
  exact movingBand_canonicalSector_observed_trace_limit N hN T S σ e hδ hAd B W C D hB hC
    K hc he hK hm ε hε hp (fun _ => 1) (fun _ => ContinuousLinearMap.norm_id_le)

#print axioms movingParityColumn_energy
#print axioms movingBand_canonicalSector_observed_trace_limit
#print axioms movingBand_canonicalSector_trace_limit
end QuantitativeMaass.Scheduled
