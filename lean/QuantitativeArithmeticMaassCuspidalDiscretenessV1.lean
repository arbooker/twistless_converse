module
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import QuantitativeArithmeticMaassCuspLocalizationV1
public import QuantitativeMaassLVCuspidalProjectionV1
public import QuantitativeMaassShiftedWaveGeneratorIdentificationV1
public import QuantitativeMaassShiftedWaveStrongLimitV1
public import QuantitativeMaassShiftedWaveTaylorV1
public import QuantitativeMaassSpectralCutoffOperatorV1

/-! Discreteness on the geometric cuspidal Hilbert space.

A short positive wave packet and cusp localization prove finite-dimensional
bounded spectral bands. The geometric cusp projection reduces the wave,
its generator and its resolvent. Finite-rank spectral cutoffs then prove
compactness of the actual cuspidal resolvent. The compact self-adjoint spectral
theorem gives dense eigenspaces and finite multiplicities, and these vectors
satisfy the actual Friedrichs graph equation. No spectral completeness or
trace-formula hypothesis is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
@[expose] public noncomputable section
open Set MeasureTheory UpperHalfPlane Matrix
open scoped Topology ENNReal ContDiff MatrixGroups
namespace QuantitativeArithmeticMaassCuspBand
open QuantitativeMaass QuantitativeMaass.Wave

/-- A real nonnegative time test of small support. -/
def shortTimeWeight (R t : ℝ) : ℝ := abelCutoffReal (Real.cosh R-1) (Real.cosh t)
def shortPacketMultiplier (R e : ℝ) : ℝ :=
  ∫ t, shortTimeWeight R t * signedCosine t (e-1/4)

theorem shortTimeWeight_continuous (R : ℝ) : Continuous (shortTimeWeight R) :=
  (abelCutoffReal_smooth _).continuous.comp Real.continuous_cosh

theorem shortTimeWeight_support (R : ℝ) (hR : 0 < R) :
    Function.support (shortTimeWeight R) ⊆ Icc (-R) R := by
  intro t ht
  apply coshTimeTest_support (abelCutoff (Real.cosh R-1)) R hR.le
    (abelCutoff_radius_support R hR)
  simpa only [Function.mem_support,coshTimeTest,abelCutoff,shortTimeWeight,ne_eq,Complex.ofReal_eq_zero] using ht

theorem shortTimeWeight_compact (R : ℝ) (hR : 0 < R) : HasCompactSupport (shortTimeWeight R) :=
  (isCompact_Icc : IsCompact (Icc (-R) R)).of_isClosed_subset isClosed_closure
    (closure_minimal (shortTimeWeight_support R hR) isClosed_Icc)

theorem shortTimeWeight_mass_pos (R : ℝ) (hR : 0 < R) :
    0 < ∫ t, shortTimeWeight R t := by
  apply integral_pos_of_integrable_nonneg_nonzero (shortTimeWeight_continuous R)
    ((shortTimeWeight_continuous R).integrable_of_hasCompactSupport (shortTimeWeight_compact R hR))
    (fun t => abelCutoffReal_nonneg _ _) (x := 0)
  simp [shortTimeWeight,abelCutoffReal_one]

theorem short_signedCosine_lower (E R e t : ℝ) (he : 0 ≤ e) (heE : e ≤ E)
    (hR : 0 ≤ R) (hR1 : R ≤ 1) (ht : |t| ≤ R)
    (hsmall : 4*R^2*(E+1) ≤ 1) : 1/2 ≤ signedCosine t (e-1/4) := by
  have hab : |e-1/4| ≤ E+1 := abs_le.mpr (by constructor <;> linarith)
  have ht2 : t^2 ≤ R^2 := by nlinarith [sq_abs t,abs_nonneg t]
  have hp := mul_le_mul ht2 hab (abs_nonneg (e-1/4)) (sq_nonneg R)
  have hs := signedCosine_second_bound (ht.trans hR1) (by linarith : -(1/4:ℝ) ≤ e-1/4)
  have hs' := (abs_le.mp hs).1
  nlinarith

/-- One short test has a positive scalar lower bound throughout the whole
bounded spectral interval, including exceptional eigenvalues. -/
theorem shortPacketMultiplier_lower (E R e : ℝ) (hR : 0 < R) (hR1 : R ≤ 1)
    (hsmall : 4*R^2*(E+1) ≤ 1) (he : 0 ≤ e) (heE : e ≤ E) :
    (∫ t, shortTimeWeight R t)/2 ≤ shortPacketMultiplier R e := by
  have hw : Integrable (shortTimeWeight R) := (shortTimeWeight_continuous R).integrable_of_hasCompactSupport (shortTimeWeight_compact R hR)
  have hc : Continuous (fun t => signedCosine t (e-1/4)) := by
    unfold signedCosine
    fun_prop
  have hi : Integrable (fun t => shortTimeWeight R t * signedCosine t (e-1/4)) :=
    ((shortTimeWeight_continuous R).mul hc).integrable_of_hasCompactSupport
    (shortTimeWeight_compact R hR).mul_right
  have hm : (∫ t, shortTimeWeight R t*(1/2:ℝ)) ≤ shortPacketMultiplier R e := by
    apply integral_mono (hw.mul_const _) hi
    intro t
    by_cases ht : shortTimeWeight R t = 0
    · simp [ht]
    · exact mul_le_mul_of_nonneg_left
        (short_signedCosine_lower E R e t he heE hR.le hR1
          (abs_le.mpr (shortTimeWeight_support R hR ht)) hsmall)
        (abelCutoffReal_nonneg _ _)
  rw [integral_mul_const] at hm
  simpa only [div_eq_mul_inv,one_mul] using hm

theorem shortPacket_eigen (N : ℕ) (R : ℝ) (hR : 0 < R) {e : ℝ} (he : 0 ≤ e)
    {v : AutomorphicSpace N} (h : FriedrichsGraph N v ((e:ℂ) • v)) :
    coshWavePacket N (abelCutoff (Real.cosh R-1)) (abelCutoff_smooth _) R hR.le
      (abelCutoff_radius_support R hR) v = (shortPacketMultiplier R e : ℂ) • v := by
  rw [coshWavePacket,shiftedQuotientWavePacket_eigen N _ _ he h]
  congr 1
  rw [shortPacketMultiplier,← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with t
  simp only [coshTimeTest,abelCutoff,shortTimeWeight,Complex.ofReal_mul]

/-- Every bounded interval contains only finitely many members of an
orthonormal family of genuine cuspidal Friedrichs eigenvectors. The packet,
its uniform nonvanishing, the form-domain lift and compact mass are all
constructed here; none is an additional hypothesis. -/
theorem cuspidal_bounded_eigenfamily_finite {ι : Type*} (N : ℕ) (hN : 0 < N)
    (E : ℝ) (hE : 0 ≤ E) (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (hcusp : ∀ i, v i ∈ localCuspidalSpace N hN)
    (e : ι → ℝ) (he : ∀ i, 0 ≤ e i) (heE : ∀ i, e i ≤ E)
    (hgraph : ∀ i, FriedrichsGraph N (v i) ((e i:ℂ) • v i)) :
    (Set.univ : Set ι).Finite := by
  classical
  let : NeZero N := ⟨hN.ne'⟩
  choose u hu hform using fun i => (friedrichsGraph_iff_form N _ _).mp (hgraph i)
  have henergy (i : ι) : (quotientClosedEnergy N (u i) (u i)).re ≤ E*‖energyInclusion N (u i)‖^2 := by
    have hself : (inner ℂ (v i) (v i)).re = ‖v i‖^2 := inner_self_eq_norm_sq (𝕜:=ℂ) _
    rw [hform i (u i),hu i,inner_smul_right (𝕜:=ℂ) (v i) (v i) (e i:ℂ),
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,hself]
    exact mul_le_mul_of_nonneg_right (heE i) (sq_nonneg ‖v i‖)
  let R : ℝ := 1/(4*(E+1))
  have hd : 0 < 4*(E+1) := by positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hR1 : R ≤ 1 := by
    dsimp [R]
    apply (div_le_one hd).mpr
    linarith
  have hReq : R*(4*(E+1)) = 1 := by
    dsimp [R]
    exact div_mul_cancel₀ 1 hd.ne'
  have hsmall : 4*R^2*(E+1) ≤ 1 := by
    calc
      _ = R*(R*(4*(E+1))) := by ring
      _ = R := by rw [hReq,mul_one]
      _ ≤ 1 := hR1
  let C : ℝ := 8*(Nat.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N):ℝ)*N^2*(N+1)*E
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let Y : ℝ := 2+Real.sqrt C
  have hY : 2 ≤ Y := by dsimp [Y]; linarith [Real.sqrt_nonneg C]
  have hsize : C ≤ Y^2 := by
    dsimp [Y]
    nlinarith [Real.sq_sqrt hC,Real.sqrt_nonneg C]
  let F := abelCutoff (Real.cosh R-1)
  have hFc : HasCompactSupport F := abelCutoff_compact _ (sub_pos.mpr (Real.one_lt_cosh.mpr hR.ne'))
  have hFs : Function.support F ⊆ Iic (Real.cosh R) := abelCutoff_radius_support R hR
  have hFr (q : ℝ) : star (F q) = F q := by simp [F,abelCutoff]
  let g := abelProfile F
  have hg : ContDiff ℝ ∞ g := abelProfile_smooth F (abelCutoff_smooth _) hFc
  have hgr (q : ℝ) : star (g q) = g q := abelProfile_real F hFr q
  have hgs : Function.support g ⊆ Iic (Real.cosh R) := abelProfile_support F _ hFs
  let b : ℝ := (∫ t, shortTimeWeight R t)/2
  have hb : 0 < b := div_pos (shortTimeWeight_mass_pos R hR) (by norm_num)
  apply cuspidal_packet_family_finite N hN u
    (by simpa only [hu] using hv) (fun i => by simpa only [hu] using hcusp i)
    E Y hY hsize henergy g hg hgr R hR.le hgs
    (fun i => (shortPacketMultiplier R (e i) : ℂ)) b hb
  · intro i
    simp only [Complex.norm_real,Real.norm_eq_abs]
    exact (shortPacketMultiplier_lower E R (e i) hR hR1 hsmall (he i) (heE i)).trans (le_abs_self _)
  · intro i
    rw [hu i]
    change abelKernelOperator N F (abelCutoff_smooth _) hFc R hR.le hFs (v i) = _
    rw [abelKernelOperator_eq_coshWavePacket N F (abelCutoff_smooth _) hFc hFr R hR.le hFs]
    exact shortPacket_eigen N R hR (he i) (hgraph i)

#print axioms cuspidal_bounded_eigenfamily_finite

#print axioms shortTimeWeight_mass_pos
#print axioms short_signedCosine_lower
#print axioms shortPacketMultiplier_lower
#print axioms shortPacket_eigen
end QuantitativeArithmeticMaassCuspBand
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
@[expose] public noncomputable section
open Set MeasureTheory UpperHalfPlane Matrix
open scoped Topology ENNReal ContDiff MatrixGroups
namespace QuantitativeArithmeticMaassCuspBand
open QuantitativeMaass QuantitativeMaass.Wave

/-- The shifted wave approaches identity uniformly on a graph-norm ball.
This estimate applies to arbitrary domain vectors, not just eigenvectors. -/
theorem shiftedWave_graph_difference (N : ℕ) (v w : AutomorphicSpace N)
    (hgraph : FriedrichsGraph N v w) (t : ℝ) (ht : |t| ≤ 1) :
    ‖shiftedQuotientWave N t v-v‖ ≤ 2*t^2*‖v+w‖ := by
  by_cases ht0 : t = 0
  · subst t
    simp only [shiftedQuotientWave_zero,ContinuousLinearMap.id_apply,sub_self,norm_zero,
      zero_pow (by norm_num : 2≠0),mul_zero,zero_mul,le_refl]
  let A := friedrichsResolvent N
  have hs : IsSelfAdjoint A := friedrichsResolvent_isSelfAdjoint N
  have hbound := shiftedOneResolventDifference_norm_le A (friedrichsResolvent_isPositive N)
    (friedrichsResolvent_opNorm_le N) ht
  have he : shiftedDampedOperator A t-A = (t^2/2:ℝ) • shiftedOneResolventDifference A t := by
    rw [shiftedOneResolventDifference_formula A hs,smul_smul]
    have hc : t^2/2*(2/t^2) = (1:ℝ) := by field_simp
    rw [hc,one_smul]
  have hd : ‖shiftedDampedOperator A t-A‖ ≤ 2*t^2 := by
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    calc
      _ ≤ (t^2/2)*4 := mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = _ := by ring
  have hh : A (v+w) = v := hgraph
  have hid : shiftedQuotientWave N t v-v = (shiftedDampedOperator A t-A) (v+w) := by
    change shiftedQuotientWave N t v-v = shiftedDampedOperator A t (v+w)-A (v+w)
    rw [← shiftedQuotientWave_resolvent N t (v+w),hh]
  rw [hid]
  exact ((shiftedDampedOperator A t-A).le_opNorm (v+w)).trans
    (mul_le_mul_of_nonneg_right hd (norm_nonneg _))

/-- After division by the positive test mass, this gives a uniform packet
approximation on a bounded graph-norm set. The mass cancels in localization. -/
theorem shortPacket_graph_difference (N : ℕ) (R : ℝ) (hR : 0 < R) (hR1 : R ≤ 1)
    (v w : AutomorphicSpace N) (hgraph : FriedrichsGraph N v w) :
    ‖coshWavePacket N (abelCutoff (Real.cosh R-1)) (abelCutoff_smooth _) R hR.le
      (abelCutoff_radius_support R hR) v - ((∫ t, shortTimeWeight R t : ℝ):ℂ) • v‖ ≤
      (∫ t, shortTimeWeight R t) * (2*R^2*‖v+w‖) := by
  let F := abelCutoff (Real.cosh R-1)
  let φ := coshTimeTest F
  have hφ : Integrable φ :=
    ((abelCutoff_smooth _).continuous.comp Real.continuous_cosh).integrable_of_hasCompactSupport
      (coshTimeTest_compact F R hR.le (abelCutoff_radius_support R hR))
  have hweight := coshTimeTest_waveWeight F (abelCutoff_smooth _) R hR.le (abelCutoff_radius_support R hR)
  have hm : (∫ t, φ t) = ((∫ t, shortTimeWeight R t : ℝ):ℂ) := by
    rw [← integral_complex_ofReal]
    rfl
  have hw : Integrable (shortTimeWeight R) :=
    (shortTimeWeight_continuous R).integrable_of_hasCompactSupport (shortTimeWeight_compact R hR)
  have he : coshWavePacket N F (abelCutoff_smooth _) R hR.le (abelCutoff_radius_support R hR) v -
      ((∫ t,shortTimeWeight R t:ℝ):ℂ) • v =
      ∫ t, φ t • (shiftedQuotientWave N t v-v) := by
    simp_rw [smul_sub]
    rw [integral_sub (shiftedQuotientWave_packet_integrable N hweight v) (hφ.smul_const v),
      integral_smul_const,hm]
    rfl
  rw [he]
  calc
    _ ≤ ∫ t, ‖φ t • (shiftedQuotientWave N t v-v)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t, shortTimeWeight R t*(2*R^2*‖v+w‖) := by
      have hi : Integrable (fun t => φ t • (shiftedQuotientWave N t v-v)) := by
        convert (shiftedQuotientWave_packet_integrable N hweight v).sub (hφ.smul_const v) using 1
        funext t
        exact smul_sub (φ t) (shiftedQuotientWave N t v) v
      apply integral_mono hi.norm (hw.mul_const _)
      intro t
      have hp : ‖φ t‖ = shortTimeWeight R t := by
        simp only [φ,F,coshTimeTest,abelCutoff,shortTimeWeight,Complex.norm_real,
          Real.norm_eq_abs,abs_of_nonneg (abelCutoffReal_nonneg _ _)]
      change ‖φ t • (shiftedQuotientWave N t v-v)‖ ≤ shortTimeWeight R t*(2*R^2*‖v+w‖)
      rw [norm_smul,hp]
      by_cases hz : shortTimeWeight R t = 0
      · simp only [hz,zero_mul,le_refl]
      · have ht := abs_le.mpr (shortTimeWeight_support R hR hz)
        apply mul_le_mul_of_nonneg_left _ (abelCutoffReal_nonneg _ _)
        apply (shiftedWave_graph_difference N v w hgraph t (ht.trans hR1)).trans
        have ht2 : t^2 ≤ R^2 := by nlinarith [sq_abs t,abs_nonneg t]
        exact mul_le_mul_of_nonneg_right (by nlinarith : 2*t^2 ≤ 2*R^2) (norm_nonneg _)
    _ = _ := integral_mul_const _ _

/-- Finiteness under a graph-norm bound, with no eigenvector hypothesis.
Thus the argument controls arbitrary vectors in a bounded spectral interval,
not merely those already known to belong to discrete eigenspaces. -/
theorem cuspidal_graph_bounded_family_finite {ι : Type*} (N : ℕ) (hN : 0 < N)
    (E : ℝ) (hE : 0 ≤ E) (v w : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (hcusp : ∀ i, v i ∈ localCuspidalSpace N hN)
    (hgraph : ∀ i, FriedrichsGraph N (v i) (w i)) (hw : ∀ i, ‖w i‖ ≤ E) :
    (Set.univ : Set ι).Finite := by
  classical
  let : NeZero N := ⟨hN.ne'⟩
  choose u hu hform using fun i => (friedrichsGraph_iff_form N _ _).mp (hgraph i)
  have henergy (i : ι) : (quotientClosedEnergy N (u i) (u i)).re ≤ E*‖energyInclusion N (u i)‖^2 := by
    rw [hform i (u i),hu i,hv.norm_eq_one i,one_pow,mul_one]
    apply (re_inner_le_norm (𝕜:=ℂ) (v i) (w i)).trans
    simpa only [hv.norm_eq_one i,one_mul] using hw i
  let C : ℝ := 8*(Nat.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N):ℝ)*N^2*(N+1)*E
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let Y : ℝ := 2+Real.sqrt C
  have hY : 2 ≤ Y := by dsimp [Y]; linarith [Real.sqrt_nonneg C]
  have hsize : C ≤ Y^2 := by dsimp [Y]; nlinarith [Real.sq_sqrt hC,Real.sqrt_nonneg C]
  let K := QuantitativeSpectralObservability.wideCompactCover N Y
  have hK := QuantitativeSpectralObservability.wideCompactCover_compact N hN Y
  let A := quotientRestriction N K hK hK.measurableSet
  have hcore (i : ι) : 1/2 ≤ ‖A (v i)‖ := by
    have h := cuspidal_bounded_energy_core N hN E Y hY hsize (u i)
      (by simpa only [hu] using hcusp i) (henergy i)
    rw [hu i,hv.norm_eq_one i,one_pow] at h
    change 1 ≤ 2*‖A (v i)‖^2 at h
    nlinarith [norm_nonneg (A (v i))]
  let D : ℝ := 8*(‖A‖+1)*(E+1)
  have hD : 0 < D := by dsimp [D]; positivity
  let R : ℝ := 1/D
  have hR : 0 < R := by dsimp [R]; positivity
  have hR1 : R ≤ 1 := by
    apply (div_le_one hD).mpr
    dsimp [D]
    nlinarith [norm_nonneg A,mul_nonneg (norm_nonneg A) hE]
  have hReq : R*D = 1 := div_mul_cancel₀ 1 hD.ne'
  have hsmall : 2*R^2*‖A‖*(E+1) ≤ 1/4 := by
    have hb : 8*(R*‖A‖*(E+1)) ≤ 1 := by
      calc
        _ ≤ 8*(R*(‖A‖+1)*(E+1)) := by gcongr; linarith
        _ = 1 := by dsimp [D] at hReq; nlinarith [hReq]
    have hR2 : R^2 ≤ R := by nlinarith
    calc
      _ ≤ 2*R*‖A‖*(E+1) := by gcongr
      _ ≤ 1/4 := by linarith
  let F := abelCutoff (Real.cosh R-1)
  have hFc : HasCompactSupport F := abelCutoff_compact _ (sub_pos.mpr (Real.one_lt_cosh.mpr hR.ne'))
  have hFs : Function.support F ⊆ Iic (Real.cosh R) := abelCutoff_radius_support R hR
  have hFr (q : ℝ) : star (F q) = F q := by simp [F,abelCutoff]
  let g := abelProfile F
  have hg : ContDiff ℝ ∞ g := abelProfile_smooth F (abelCutoff_smooth _) hFc
  have hgr (q : ℝ) : star (g q) = g q := abelProfile_real F hFr q
  have hgs : Function.support g ⊆ Iic (Real.cosh R) := abelProfile_support F _ hFs
  let P := radialKernelOperator N g hg R hR.le hgs
  have hP : P = coshWavePacket N F (abelCutoff_smooth _) R hR.le hFs :=
    abelKernelOperator_eq_coshWavePacket N F (abelCutoff_smooth _) hFc hFr R hR.le hFs
  let m : ℝ := ∫ t, shortTimeWeight R t
  have hm : 0 < m := shortTimeWeight_mass_pos R hR
  have hdelta (i : ι) : ‖A (P (v i)) - (m:ℂ) • A (v i)‖ ≤ m/4 := by
    have hd := shortPacket_graph_difference N R hR hR1 (v i) (w i) (hgraph i)
    rw [← hP] at hd
    change ‖P (v i)-(m:ℂ) • v i‖ ≤ m*(2*R^2*‖v i+w i‖) at hd
    have hn : ‖v i+w i‖ ≤ E+1 := (norm_add_le _ _).trans (by rw [hv.norm_eq_one i]; linarith [hw i])
    rw [← map_smul,← map_sub]
    calc
      _ ≤ ‖A‖*‖P (v i)-(m:ℂ) • v i‖ := A.le_opNorm _
      _ ≤ ‖A‖*(m*(2*R^2*‖v i+w i‖)) := mul_le_mul_of_nonneg_left hd (norm_nonneg A)
      _ = m*(2*R^2*‖A‖*‖v i+w i‖) := by ring
      _ ≤ m*(2*R^2*‖A‖*(E+1)) := by gcongr
      _ ≤ m*(1/4) := mul_le_mul_of_nonneg_left hsmall hm.le
      _ = m/4 := by ring
  have hf := radialKernel_finite_raw_threshold N v hv g hg hgr R hR.le hgs K hK
    (ENNReal.ofReal ((m/4)^2)) (by positivity)
  apply hf.subset
  intro i _
  apply ENNReal.ofReal_le_ofReal
  change (m/4)^2 ≤ ‖A (P (v i))‖^2
  have ht := norm_sub_norm_le ((m:ℂ) • A (v i)) (A (P (v i)))
  rw [norm_sub_rev,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hm] at ht
  have hc := mul_le_mul_of_nonneg_left (hcore i) hm.le
  have hd := hdelta i
  have hl : m/4 ≤ ‖A (P (v i))‖ := by nlinarith
  nlinarith [norm_nonneg (A (P (v i)))]

#print axioms cuspidal_graph_bounded_family_finite

#print axioms shiftedWave_graph_difference
#print axioms shortPacket_graph_difference
end QuantitativeArithmeticMaassCuspBand
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
@[expose] public noncomputable section
open Set MeasureTheory UpperHalfPlane Matrix
open scoped Topology ENNReal ContDiff MatrixGroups
namespace QuantitativeArithmeticMaassCuspBand
open QuantitativeMaass QuantitativeMaass.Wave

/-- A closed cuspidal subspace on which the actual Laplacian has bounded
norm is finite dimensional. No spectral decomposition is assumed. -/
theorem closed_cuspidal_graph_subspace_finiteDimensional (N : ℕ) (hN : 0 < N)
    (E : ℝ) (hE : 0 ≤ E) (S : Submodule ℂ (AutomorphicSpace N))
    (hS : IsClosed (S : Set (AutomorphicSpace N))) (hcusp : S ≤ localCuspidalSpace N hN)
    (hgraph : ∀ v ∈ S, ∃ w, FriedrichsGraph N v w ∧ ‖w‖ ≤ E*‖v‖) :
    FiniteDimensional ℂ S := by
  classical
  let : CompleteSpace S := hS.completeSpace_coe
  obtain ⟨J,b,_⟩ := exists_hilbertBasis ℂ S
  let v := fun i : J => (b i : AutomorphicSpace N)
  have hv : Orthonormal ℂ v := b.orthonormal.comp_linearIsometry S.subtypeₗᵢ
  choose w hw hbound using fun i => hgraph (v i) (b i).property
  have hf := cuspidal_graph_bounded_family_finite N hN E hE v w hv
    (fun i => hcusp (b i).property) hw
    (fun i => by simpa only [hv.norm_eq_one i,mul_one] using hbound i)
  let : Finite J := Set.finite_univ_iff.mp hf
  let : Fintype J := Fintype.ofFinite J
  exact b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- Closed range support of the continuous low-energy spectral cutoff. -/
def boundedSpectralSpace (N : ℕ) (ε : ℝ) : Submodule ℂ (AutomorphicSpace N) :=
  (LinearMap.range (resolventCutoffOperator (friedrichsResolvent N) ε).toLinearMap).topologicalClosure

/-- The exact regularized-generator identity passes to the whole closed
spectral subspace, not merely the image of the cutoff. -/
theorem boundedSpectralSpace_graph (N : ℕ) (ε : ℝ) (hε : 0 < ε)
    (v : AutomorphicSpace N) (hv : v ∈ boundedSpectralSpace N ε) :
    FriedrichsGraph N v (boundedResolventOperator (friedrichsResolvent N) ε v) := by
  let B := boundedResolventOperator (friedrichsResolvent N) ε
  have hc : IsClosed {x : AutomorphicSpace N | FriedrichsGraph N x (B x)} := by
    change IsClosed {x : AutomorphicSpace N | friedrichsResolvent N (x+B x) = x}
    apply isClosed_eq <;> fun_prop
  have hs : (LinearMap.range (resolventCutoffOperator (friedrichsResolvent N) ε).toLinearMap :
      Set (AutomorphicSpace N)) ⊆ {x | FriedrichsGraph N x (B x)} := by
    rintro _ ⟨x,rfl⟩
    exact friedrichsCutoff_graph N ε hε x
  exact closure_minimal hs hc hv

/-- Every bounded spectral band in the actual geometric cusp space is
finite dimensional, including any continuous spectral contribution. -/
theorem cuspidal_boundedSpectralSpace_finiteDimensional (N : ℕ) (hN : 0 < N)
    (ε : ℝ) (hε : 0 < ε) :
    FiniteDimensional ℂ ↥(localCuspidalSpace N hN ⊓ boundedSpectralSpace N ε) := by
  apply closed_cuspidal_graph_subspace_finiteDimensional N hN (ε⁻¹+1) (by positivity)
    (localCuspidalSpace N hN ⊓ boundedSpectralSpace N ε)
  · exact (localCuspidalSpace_closed N hN).inter
      (LinearMap.range (resolventCutoffOperator (friedrichsResolvent N) ε).toLinearMap).isClosed_topologicalClosure
  · exact inf_le_left
  · intro v hv
    refine ⟨boundedResolventOperator (friedrichsResolvent N) ε v,
      boundedSpectralSpace_graph N ε hε v hv.2,?_⟩
    exact ((boundedResolventOperator (friedrichsResolvent N) ε).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right
        (boundedResolventOperator_norm_le (friedrichsResolvent N) ε hε) (norm_nonneg v))

#print axioms closed_cuspidal_graph_subspace_finiteDimensional
#print axioms boundedSpectralSpace_graph
#print axioms cuspidal_boundedSpectralSpace_finiteDimensional
end QuantitativeArithmeticMaassCuspBand
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
namespace QuantitativeArithmeticMaassCuspBand
open QuantitativeMaass QuantitativeMaass.Wave

/-- The geometric cusp projection reduces every shifted wave operator. -/
theorem cuspProjection_commute_wave (N : ℕ) (hN : 0 < N) (t : ℝ) :
    Commute (localCuspidalProjection N hN) (shiftedQuotientWave N t) := by
  let P := localCuspidalProjection N hN
  let B := shiftedQuotientWave N t
  have hPB : P*B*P = B*P := by
    apply ContinuousLinearMap.ext
    intro f
    apply Submodule.starProjection_eq_self_iff.mpr
    exact shiftedQuotientWave_mem_localCuspidalSpace N hN (P f)
      ((localCuspidalSpace N hN).starProjection_apply_mem f) t
  have hp : P.adjoint = P := (localCuspidalProjection_selfAdjoint N hN).adjoint_eq
  have hb : B.adjoint = B := (shiftedQuotientWave_isSelfAdjoint N t).adjoint_eq
  have hBP := congrArg ContinuousLinearMap.adjoint hPB
  change ((P.comp B).comp P).adjoint = (B.comp P).adjoint at hBP
  simp only [ContinuousLinearMap.adjoint_comp,hp,hb] at hBP
  change P*(B*P) = P*B at hBP
  rw [← mul_assoc] at hBP
  exact hBP.symm.trans hPB

/-- Commutation with the wave passes through its proved generator limit
and hence preserves the full actual Friedrichs operator domain. -/
theorem cuspProjection_graph (N : ℕ) (hN : 0 < N) (v w : AutomorphicSpace N)
    (hgraph : FriedrichsGraph N v w) :
    FriedrichsGraph N (localCuspidalProjection N hN v) (localCuspidalProjection N hN w) := by
  let P := localCuspidalProjection N hN
  apply (shiftedQuotientWave_generator_iff N (P v) (P w)).mpr
  have ht := P.continuous.tendsto ((1/4:ℂ) • v-w) |>.comp (shiftedQuotientWave_generator N hgraph)
  have he (t : ℝ) : P (shiftedQuotientTimeDifference N t v) = shiftedQuotientTimeDifference N t (P v) := by
    have hc := congrArg (fun A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N => A v)
      (cuspProjection_commute_wave N hN t).eq
    change P (shiftedQuotientWave N t v) = shiftedQuotientWave N t (P v) at hc
    change P ((2/t^2:ℝ) • (shiftedQuotientWave N t v-v)) =
      (2/t^2:ℝ) • (shiftedQuotientWave N t (P v)-P v)
    calc
      _ = (2/t^2:ℝ) • P (shiftedQuotientWave N t v-v) :=
        (P.restrictScalars ℝ).map_smul (2/t^2) (shiftedQuotientWave N t v-v)
      _ = _ := by rw [map_sub,hc]
  simpa only [Function.comp_def,he,map_sub,map_smul] using ht

/-- The actual resolvent reduces the closed all-cusp kernel. -/
theorem cuspProjection_commute_resolvent (N : ℕ) (hN : 0 < N) :
    Commute (localCuspidalProjection N hN) (friedrichsResolvent N) := by
  let P := localCuspidalProjection N hN
  let A := friedrichsResolvent N
  apply ContinuousLinearMap.ext
  intro v
  have h := cuspProjection_graph N hN (A v) (v-A v) (friedrichsGraph_resolvent N v)
  change A (P (A v)+P (v-A v)) = P (A v) at h
  rw [← map_add,add_sub_cancel] at h
  exact h.symm

theorem cutoffOperator_commute_of_commute {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : H →L[ℂ] H) (h : Commute B A) (ε : ℝ) :
    Commute B (resolventCutoffOperator A ε) :=
  (h.symm.cfc_real (resolventCutoff ε)).symm

/-- Every low-energy functional-calculus cutoff preserves cuspidality. -/
theorem cuspProjection_commute_cutoff (N : ℕ) (hN : 0 < N) (ε : ℝ) :
    Commute (localCuspidalProjection N hN) (resolventCutoffOperator (friedrichsResolvent N) ε) :=
  cutoffOperator_commute_of_commute _ _ (cuspProjection_commute_resolvent N hN) ε

theorem cutoff_mem_localCuspidalSpace (N : ℕ) (hN : 0 < N) (ε : ℝ)
    (v : AutomorphicSpace N) (hv : v ∈ localCuspidalSpace N hN) :
    resolventCutoffOperator (friedrichsResolvent N) ε v ∈ localCuspidalSpace N hN := by
  apply Submodule.starProjection_eq_self_iff.mp
  have hp : localCuspidalProjection N hN v = v := Submodule.starProjection_eq_self_iff.mpr hv
  have hc := congrArg (fun B : AutomorphicSpace N →L[ℂ] AutomorphicSpace N => B v)
    (cuspProjection_commute_cutoff N hN ε).eq
  change localCuspidalProjection N hN (resolventCutoffOperator (friedrichsResolvent N) ε v) =
    resolventCutoffOperator (friedrichsResolvent N) ε (localCuspidalProjection N hN v) at hc
  rw [hp] at hc
  exact hc

#print axioms cuspProjection_commute_cutoff
#print axioms cutoff_mem_localCuspidalSpace

#print axioms cuspProjection_commute_wave
#print axioms cuspProjection_graph
#print axioms cuspProjection_commute_resolvent
end QuantitativeArithmeticMaassCuspBand
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace QuantitativeArithmeticMaassCuspBand
open QuantitativeMaass QuantitativeMaass.Wave

/-- A low-energy cutoff of the cuspidal resolvent has finite-dimensional
range, hence is compact. This is derived from localization and Bessel. -/
theorem cuspidal_cutoff_resolvent_compact (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    IsCompactOperator (resolventCutoffOperator (friedrichsResolvent N) ε *
      friedrichsResolvent N * localCuspidalProjection N hN) := by
  let A := friedrichsResolvent N
  let P := localCuspidalProjection N hN
  let C := resolventCutoffOperator A ε
  let W := localCuspidalSpace N hN ⊓ boundedSpectralSpace N ε
  let : FiniteDimensional ℂ W := cuspidal_boundedSpectralSpace_finiteDimensional N hN ε hε
  let T := C*A*P
  have hm (v : AutomorphicSpace N) : T v ∈ W := by
    constructor
    · have ha : A (P v) ∈ localCuspidalSpace N hN := by
        have he := congrArg (fun B : AutomorphicSpace N →L[ℂ] AutomorphicSpace N => B v)
          (cuspProjection_commute_resolvent N hN).eq
        change P (A v) = A (P v) at he
        rw [← he]
        exact (localCuspidalSpace N hN).starProjection_apply_mem (A v)
      exact cutoff_mem_localCuspidalSpace N hN ε (A (P v)) ha
    · apply (LinearMap.range C.toLinearMap).le_topologicalClosure
      exact ⟨A (P v),rfl⟩
  have hc := isCompactOperator_of_locallyCompactSpace_dom (T.codRestrict W hm)
  exact hc.clm_comp W.subtypeL

/-- The actual resolvent followed by the geometric cusp projection is
compact, as an operator-norm limit of the finite-rank cutoffs above. -/
theorem cuspidal_resolvent_compact (N : ℕ) (hN : 0 < N) :
    IsCompactOperator (friedrichsResolvent N * localCuspidalProjection N hN) := by
  let A := friedrichsResolvent N
  let P := localCuspidalProjection N hN
  let F := fun ε : ℝ => resolventCutoffOperator A ε*A*P
  have hb (ε : ℝ) (hε : 0 < ε) : ‖F ε-A*P‖ ≤ ε*‖P‖ := by
    have he : F ε-A*P = ((resolventCutoffOperator A ε-1)*A)*P := by
      dsimp only [F]
      rw [sub_mul,one_mul,sub_mul]
    rw [he]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
      (resolventCutoffOperator_residual_norm A (friedrichsResolvent_isPositive N)
        (friedrichsResolvent_opNorm_le N) ε hε) (norm_nonneg P))
  have hl : Tendsto F (𝓝[>] (0:ℝ)) (𝓝 (A*P)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hz : Tendsto (fun ε : ℝ => F ε-A*P) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      apply squeeze_zero_norm'
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        exact hb ε hε
      · have hi : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
        simpa only [zero_mul] using hi.mul_const ‖P‖
    simpa only [norm_zero] using hz.norm
  apply isCompactOperator_of_tendsto hl
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact cuspidal_cutoff_resolvent_compact N hN ε hε

#print axioms cuspidal_cutoff_resolvent_compact
#print axioms cuspidal_resolvent_compact
end QuantitativeArithmeticMaassCuspBand
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
namespace QuantitativeArithmeticMaassCuspBand
open QuantitativeMaass QuantitativeMaass.Wave

theorem resolvent_mem_localCuspidalSpace (N : ℕ) (hN : 0 < N)
    (v : AutomorphicSpace N) (hv : v ∈ localCuspidalSpace N hN) :
    friedrichsResolvent N v ∈ localCuspidalSpace N hN := by
  apply Submodule.starProjection_eq_self_iff.mp
  have hp : localCuspidalProjection N hN v = v := Submodule.starProjection_eq_self_iff.mpr hv
  have hc := congrArg (fun B : AutomorphicSpace N →L[ℂ] AutomorphicSpace N => B v)
    (cuspProjection_commute_resolvent N hN).eq
  change localCuspidalProjection N hN (friedrichsResolvent N v) =
    friedrichsResolvent N (localCuspidalProjection N hN v) at hc
  rw [hp] at hc
  exact hc

/-- The actual Friedrichs resolvent restricted to the geometric all-cusp kernel. -/
def cuspidalResolvent (N : ℕ) (hN : 0 < N) :
    localCuspidalSpace N hN →L[ℂ] localCuspidalSpace N hN :=
  (friedrichsResolvent N).restrict (resolvent_mem_localCuspidalSpace N hN)

theorem cuspidalResolvent_compact (N : ℕ) (hN : 0 < N) :
    IsCompactOperator (cuspidalResolvent N hN) := by
  let S := localCuspidalSpace N hN
  have hc := (cuspidal_resolvent_compact N hN).comp_clm S.subtypeL
  have he : (friedrichsResolvent N * localCuspidalProjection N hN).comp S.subtypeL =
      (friedrichsResolvent N).comp S.subtypeL := by
    apply ContinuousLinearMap.ext
    intro v
    change friedrichsResolvent N (localCuspidalProjection N hN v) = friedrichsResolvent N v
    rw [show localCuspidalProjection N hN v = v from
      Submodule.starProjection_eq_self_iff.mpr v.property]
  change IsCompactOperator ((friedrichsResolvent N * localCuspidalProjection N hN).comp S.subtypeL) at hc
  rw [he] at hc
  exact hc.codRestrict (fun v => resolvent_mem_localCuspidalSpace N hN v v.property)
    (localCuspidalSpace_closed N hN)

theorem cuspidalResolvent_symmetric (N : ℕ) (hN : 0 < N) :
    LinearMap.IsSymmetric (𝕜 := ℂ) (E := ↥(localCuspidalSpace N hN))
      (cuspidalResolvent N hN).toLinearMap :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (friedrichsResolvent_isSelfAdjoint N)).restrict_invariant
      (resolvent_mem_localCuspidalSpace N hN)

theorem cuspidalResolvent_injective (N : ℕ) (hN : 0 < N) :
    Function.Injective (cuspidalResolvent N hN) := by
  intro v w h
  apply Subtype.ext
  exact friedrichsResolvent_injective N (congrArg Subtype.val h)

/-- Completeness of the genuine cuspidal resolvent eigenspaces. -/
theorem cuspidal_eigenspaces_dense (N : ℕ) (hN : 0 < N) :
    (⨆ μ : ℂ, Module.End.eigenspace (R := ℂ) (M := ↥(localCuspidalSpace N hN))
      (cuspidalResolvent N hN).toLinearMap μ).topologicalClosure = ⊤ := by
  apply (Submodule.orthogonal_eq_bot_iff (𝕜 := ℂ)
    (E := ↥(localCuspidalSpace N hN))).mp
  rw [Submodule.orthogonal_closure]
  exact ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot (𝕜 := ℂ)
    (E := ↥(localCuspidalSpace N hN))
    (cuspidalResolvent_compact N hN) (cuspidalResolvent_symmetric N hN)

def cuspidalResolventEigenspace (N : ℕ) (hN : 0 < N) (μ : ℂ) :
    Submodule ℂ ↥(localCuspidalSpace N hN) :=
  Module.End.eigenspace (R := ℂ) (M := ↥(localCuspidalSpace N hN))
    (cuspidalResolvent N hN).toLinearMap μ

theorem cuspidal_resolvent_eigenspace_finiteDimensional (N : ℕ) (hN : 0 < N)
    (μ : ℂ) (hμ : μ ≠ 0) :
    Module.Finite ℂ ↥(cuspidalResolventEigenspace N hN μ) :=
  ContinuousLinearMap.finite_dimensional_eigenspace (𝕜 := ℂ)
    (E := ↥(localCuspidalSpace N hN)) (cuspidalResolvent_compact N hN) μ hμ

theorem cuspidalResolventEigenspace_zero (N : ℕ) (hN : 0 < N) :
    cuspidalResolventEigenspace N hN 0 = ⊥ := by
  apply le_antisymm
  · intro v hv
    rw [Submodule.mem_bot]
    apply cuspidalResolvent_injective N hN
    have he := Module.End.mem_eigenspace_iff.mp hv
    change cuspidalResolvent N hN v = (0 : ℂ) • v at he
    rw [zero_smul] at he
    exact he.trans (map_zero (cuspidalResolvent N hN)).symm
  · exact bot_le

/-- Resolvent eigenvectors are eigenvectors of the actual unbounded
Friedrichs realization, with the reciprocal eigenvalue transformation. -/
theorem cuspidal_resolvent_eigenvector_graph (N : ℕ) (hN : 0 < N)
    (μ : ℂ) (hμ : μ ≠ 0) (v : localCuspidalSpace N hN)
    (hv : v ∈ cuspidalResolventEigenspace N hN μ) :
    FriedrichsGraph N v ((μ⁻¹-1) • (v : AutomorphicSpace N)) := by
  have he : friedrichsResolvent N v = μ • (v : AutomorphicSpace N) :=
    congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp hv)
  have hs : (v : AutomorphicSpace N)+(μ⁻¹-1) • (v : AutomorphicSpace N) =
      μ⁻¹ • (v : AutomorphicSpace N) := by
    calc
      _ = (1+(μ⁻¹-1)) • (v : AutomorphicSpace N) := by rw [add_smul,one_smul]
      _ = _ := by congr 1; ring
  change friedrichsResolvent N ((v : AutomorphicSpace N)+(μ⁻¹-1) • (v : AutomorphicSpace N)) = v
  rw [hs,map_smul,he,smul_smul,inv_mul_cancel₀ hμ,one_smul]

#print axioms cuspidalResolvent_compact
#print axioms cuspidalResolvent_injective
#print axioms cuspidal_eigenspaces_dense
#print axioms cuspidal_resolvent_eigenspace_finiteDimensional
#print axioms cuspidalResolventEigenspace_zero
#print axioms cuspidal_resolvent_eigenvector_graph
end QuantitativeArithmeticMaassCuspBand
end
