module

public import QuantitativeSpectralObservabilityCoverV1
public import QuantitativeMaassRadialKernelSymmetryV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceLabels AsymptoticCongruenceStrip AsymptoticHyperbolicArea
open QuantitativeSpectralObservability
open scoped ENNReal NNReal Pointwise MatrixGroups

namespace QuantitativeMaass

/-- A fixed finite-area envelope for every compact cusp cutoff. -/
def cuspCoreEnvelope : Set ℍ :=
  {z | -2 ≤ z.re ∧ z.re < 3 ∧ (1:ℝ)/8 < z.im}

theorem cuspCoreEnvelope_measurable : MeasurableSet cuspCoreEnvelope :=
  (measurableSet_Ici.preimage continuous_re.measurable).inter
    ((measurableSet_Iio.preimage continuous_re.measurable).inter
      (measurableSet_Ioi.preimage continuous_im.measurable))

theorem cuspCoreEnvelope_area : (volume : Measure ℍ) cuspCoreEnvelope = 40 := by
  have he : UpperHalfPlane.coe '' cuspCoreEnvelope =
      Complex.measurableEquivRealProd.symm '' (Ico (-2:ℝ) 3 ×ˢ Ioi ((1:ℝ)/8)) := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact ⟨(w.re,w.im),⟨⟨hw.1,hw.2.1⟩,hw.2.2⟩,rfl⟩
    · rintro ⟨⟨x,y⟩,hxy,rfl⟩
      exact ⟨⟨⟨x,y⟩,lt_trans (by norm_num : (0:ℝ)<1/8) hxy.2⟩,
        ⟨hxy.1.1,hxy.1.2,hxy.2⟩,rfl⟩
  rw [UpperHalfPlane.volume_eq_lintegral,he]
  rw [← (Complex.volume_preserving_equiv_real_prod.symm _).setLIntegral_comp_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding]
  change (∫⁻ p : ℝ×ℝ in Ico (-2:ℝ) 3 ×ˢ Ioi ((1:ℝ)/8),
    (↑((1/‖p.2‖₊)^2 : ℝ≥0) : ℝ≥0∞))=40
  rw [Measure.volume_eq_prod,setLIntegral_prod _ (by fun_prop)]
  simp only [vertical_area (by norm_num : (0:ℝ)<1/8)]
  norm_num

theorem wideBox_area_uniform (H : ℝ) :
    (volume : Measure ℍ) (wideBox H) ≤ 40 := by
  apply (measure_mono (show wideBox H ⊆ cuspCoreEnvelope from ?_)).trans_eq
    cuspCoreEnvelope_area
  intro z hz
  exact ⟨by linarith [hz.1],by linarith [hz.2.1],by linarith [hz.2.2.1]⟩

/-- The raw area of the whole reduction core is uniformly bounded in its
height. This is the measure used in cusp localization, before quotienting. -/
theorem wideCompactCover_area_uniform (N : ℕ) (hN : 0<N) (H : ℝ) :
    (volume : Measure ℍ) (wideCompactCover N H) ≤
      (Nat.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N):ℝ≥0∞)*40 := by
  let : NeZero N := ⟨hN.ne'⟩
  let := Fintype.ofFinite (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  calc
    _ ≤ ∑' q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
        (volume : Measure ℍ) ((integralLabel q.out)⁻¹ • wideBox H) := measure_iUnion_le _
    _ ≤ ∑' _q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N,(40:ℝ≥0∞) := by
      apply ENNReal.tsum_le_tsum
      intro q
      rw [←preimage_smul_inv,inv_inv]
      rw [(AsymptoticRationalGroup.measurePreserving (integralLabel q.out)).measure_preimage
        (wideBox_compact H).measurableSet.nullMeasurableSet]
      exact wideBox_area_uniform H
    _ = _ := by
      simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
        Nat.card_eq_fintype_card]

/-- Exponential distance of the standard cutoff grows only quadratically
with height; the hyperbolic radius therefore grows logarithmically. -/
theorem wideBox_exp_dist (H : ℝ) (hH : 2≤H) {z : ℍ} (hz : z∈wideBox H) :
    Real.exp (dist z I) ≤ 4*(H+3)^2 := by
  have hx : z.re^2≤4 := by nlinarith [hz.1,hz.2.1]
  have hy : z.im^2≤H^2 := pow_le_pow_left₀ z.im_pos.le hz.2.2.2 2
  have hc : Real.cosh (dist z I) ≤ 2*(H^2+5) := by
    rw [UpperHalfPlane.cosh_dist']
    simp only [I_re,I_im,sub_zero,one_pow,mul_one]
    apply (div_le_iff₀ (by positivity : 0<2*z.im)).mpr
    have hp : 0≤H^2+5 := by positivity
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hz.2.2.1)]
  have he : Real.exp (dist z I)≤2*Real.cosh (dist z I) := by
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-dist z I)]
  nlinarith

/-- One level-dependent constant controls every translate and every height.
No spectral assertion is assumed in this geometric estimate. -/
theorem wideCompactCover_exp_dist (N : ℕ) (hN : 0<N) :
    ∃ C : ℝ, 1≤C ∧ ∀ H : ℝ, 2≤H → ∀ z∈wideCompactCover N H,
      Real.exp (dist z I)≤C*(H+3)^2 := by
  let : NeZero N := ⟨hN.ne'⟩
  let := Fintype.ofFinite (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  let D : ℝ := ∑ q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
    Real.exp (dist (q.out⁻¹ • I) I)
  have hD : 0≤D := Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
  refine ⟨4*D+1,by linarith,?_⟩
  intro H hH z hz
  obtain ⟨q,w,hw,rfl⟩ := mem_iUnion.mp hz
  dsimp only at *
  rw [←map_inv,integralLabel_action]
  have hq : Real.exp (dist (q.out⁻¹ • I) I)≤D := by
    exact Finset.single_le_sum (f:=fun q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N =>
      Real.exp (dist (q.out⁻¹ • I) I)) (fun _ _ => (Real.exp_pos _).le) (Finset.mem_univ q)
  have hd : dist (q.out⁻¹ • w) I ≤ dist w I+dist (q.out⁻¹ • I) I := by
    simpa only [integral_action_dist] using dist_triangle (q.out⁻¹ • w) (q.out⁻¹ • I) I
  calc
    _ ≤ Real.exp (dist w I+dist (q.out⁻¹ • I) I) := Real.exp_le_exp.mpr hd
    _ = Real.exp (dist w I)*Real.exp (dist (q.out⁻¹ • I) I) := Real.exp_add _ _
    _ ≤ (4*(H+3)^2)*D := mul_le_mul (wideBox_exp_dist H hH hw) hq
      (Real.exp_pos _).le (by positivity)
    _ ≤ (4*D+1)*(H+3)^2 := by nlinarith [sq_nonneg (H+3)]

theorem wideCompactCover_log_radius (N : ℕ) (hN : 0<N) :
    ∃ C : ℝ, 1≤C ∧ ∀ H : ℝ, 2≤H →
      wideCompactCover N H ⊆ Metric.closedBall I (Real.log (C*(H+3)^2)) := by
  obtain ⟨C,hC,h⟩ := wideCompactCover_exp_dist N hN
  refine ⟨C,hC,?_⟩
  intro H hH z hz
  exact (Real.le_log_iff_exp_le (by positivity : 0<C*(H+3)^2)).mpr (h H hH z hz)

#print axioms cuspCoreEnvelope_area
#print axioms wideBox_area_uniform
#print axioms wideCompactCover_area_uniform
#print axioms wideBox_exp_dist
#print axioms wideCompactCover_exp_dist
#print axioms wideCompactCover_log_radius

end QuantitativeMaass
