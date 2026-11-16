module

public import QuantitativeMaassWindowTailsV1
public import QuantitativeMaassSmoothPacketTraceV1
public import QuantitativeMaassShiftedPacketDomainV1
public import QuantitativeMaassWaveLocalizedPropagationV1
public import QuantitativeMaassShiftedWaveCosineV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped FourierTransform SchwartzMap ContDiff ComplexConjugate

namespace QuantitativeMaass

def complexWindowKernel (K : SchwartzMap ℝ ℝ) : SchwartzMap ℝ ℂ :=
  K.postcompCLM Complex.ofRealCLM

def kernelTimeProfile (K : SchwartzMap ℝ ℝ) (s : ℝ) : ℂ :=
  ((2*Real.pi:ℝ):ℂ)⁻¹ * (𝓕 (complexWindowKernel K) : SchwartzMap ℝ ℂ) (s/(2*Real.pi))

theorem kernelTimeProfile_smooth (K : SchwartzMap ℝ ℝ) :
    ContDiff ℝ ∞ (kernelTimeProfile K) := by
  have hf := (𝓕 (complexWindowKernel K) : SchwartzMap ℝ ℂ).smooth ⊤
  change ContDiff ℝ ∞ (fun s => ((2*Real.pi:ℝ):ℂ)⁻¹ *
    (𝓕 (complexWindowKernel K) : SchwartzMap ℝ ℂ) (s/(2*Real.pi)))
  fun_prop

theorem kernelTimeProfile_compact (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    HasCompactSupport (kernelTimeProfile K) := by
  have hF : HasCompactSupport ((𝓕 (complexWindowKernel K) : SchwartzMap ℝ ℂ) : ℝ → ℂ) := hc
  have hs : HasCompactSupport (fun s =>
      (𝓕 (complexWindowKernel K) : SchwartzMap ℝ ℂ) (s/(2*Real.pi))) := by
    simpa only [Function.comp_def,Homeomorph.coe_mulRight₀,div_eq_mul_inv] using
      hF.comp_homeomorph (Homeomorph.mulRight₀ (2*Real.pi)⁻¹ (inv_ne_zero (by positivity)))
  exact hs.mul_left

theorem kernelTimeProfile_even (K : SchwartzMap ℝ ℝ) (he : Function.Even K) :
    Function.Even (kernelTimeProfile K) := by
  have hec : Function.Even (complexWindowKernel K) := by
    intro x
    change (K (-x):ℂ)=(K x:ℂ)
    rw [he x]
  intro s
  simp only [kernelTimeProfile,neg_div]
  exact congrArg (fun z : ℂ => ((2*Real.pi:ℝ):ℂ)⁻¹*z)
    (schwartz_fourier_even _ hec (s/(2*Real.pi)))

theorem kernelTimeProfile_real (K : SchwartzMap ℝ ℝ) (he : Function.Even K) (s : ℝ) :
    star (kernelTimeProfile K s)=kernelTimeProfile K s := by
  have hec : Function.Even (complexWindowKernel K) := by
    intro x
    change (K (-x):ℂ)=(K x:ℂ)
    rw [he x]
  have hr (x : ℝ) : star (complexWindowKernel K x)=complexWindowKernel K x := by
    change star (K x:ℂ)=(K x:ℂ)
    simp
  simp only [kernelTimeProfile,map_mul,map_inv₀,Complex.star_def,Complex.conj_ofReal]
  exact congrArg (fun z : ℂ => ((2*Real.pi:ℝ):ℂ)⁻¹*z)
    (schwartz_fourier_real _ hec hr (s/(2*Real.pi)))

/-- The cosine-transform normalization is fixed exactly by Fourier
inversion; no transform-identification premise is supplied. -/
theorem kernelTimeProfile_cosinePacket (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (r : ℝ) :
    cosinePacket (kernelTimeProfile K) r=(K r:ℂ) := by
  let f := complexWindowKernel K
  let F : SchwartzMap ℝ ℂ := 𝓕 f
  have hF : HasCompactSupport (F : ℝ → ℂ) := hc
  have hFF (x : ℝ) : 𝓕 (F : ℝ → ℂ) x=f (-x) := by
    have h := congrFun (f.continuous.fourierInv_fourier_eq f.integrable F.integrable) (-x)
    rw [Real.fourierInv_eq_fourier_neg,neg_neg] at h
    exact h
  have hcos (u : ℝ) : cosinePacket F u=
      ((K (u/(2*Real.pi)):ℂ)+(K (-u/(2*Real.pi)):ℂ))/2 := by
    rw [cosinePacket,compact_cosine_packet_fourier F (F.smooth ⊤) hF]
    change (𝓕 (F : ℝ → ℂ) (-u/(2*Real.pi))+𝓕 (F : ℝ → ℂ) (u/(2*Real.pi)))/2=_
    rw [hFF,hFF]
    simp only [f,complexWindowKernel,SchwartzMap.postcompCLM_apply,
      Complex.ofRealCLM_apply,neg_div,neg_neg]
  have hp : 0<2*Real.pi := by positivity
  calc
    _ = ((2*Real.pi:ℝ):ℂ)⁻¹*cosinePacket (fun s => F (s/(2*Real.pi))) r := by
      unfold cosinePacket kernelTimeProfile
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with s
      dsimp [F,f]
      ring
    _ = ((2*Real.pi:ℝ):ℂ)⁻¹*((2*Real.pi:ℝ):ℂ)*cosinePacket F ((2*Real.pi)*r) := by
      rw [cosinePacket_dilation _ _ _ hp]
      ring
    _ = cosinePacket F ((2*Real.pi)*r) := by
      rw [inv_mul_cancel₀ (by exact_mod_cast hp.ne'),one_mul]
    _ = (K r:ℂ) := by
      rw [hcos]
      have hplus : ((2*Real.pi)*r)/(2*Real.pi)=r := by field_simp
      have hminus : -((2*Real.pi)*r)/(2*Real.pi)=-r := by field_simp
      rw [hplus,hminus,he r]
      ring

theorem integral_Icc_reflect (f : ℝ → ℝ) (a b : ℝ) :
    (∫ u in Icc (-b) (-a),f u)=(∫ u in Icc a b,f (-u)) := by
  rw [← integral_indicator measurableSet_Icc,← integral_indicator measurableSet_Icc]
  have h := integral_sub_left_eq_self ((Icc a b).indicator (fun u => f (-u))) volume (0:ℝ)
  simp only [zero_sub] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards with u
  have hm : (-u)∈Icc a b ↔ u∈Icc (-b) (-a) := by
    constructor <;> intro hu <;> constructor <;> linarith [hu.1,hu.2]
  by_cases hu : u∈Icc (-b) (-a)
  · simp [hu,hm.mpr hu]
  · have hn : -u∉Icc a b := fun h => hu (hm.mp h)
    simp [hu,hn]

theorem averaged_kernelTimeProfile_cosinePacket (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R a b r : ℝ) (hR : 0<R) :
    cosinePacket (averagedTimeTest (kernelTimeProfile K) R (volume.restrict (Icc a b))) r =
      ((smoothedWindow K R (Icc a b) r+smoothedWindow K R (Icc (-b) (-a)) r:ℝ):ℂ)/2 := by
  have hφ := kernelTimeProfile_smooth K
  have hφc := kernelTimeProfile_compact K hc
  have hid (T : ℝ) : cosinePacket (scaledModulatedTimeTest (kernelTimeProfile K) R T) r=
      ((scaledWindowKernel K R (r-T)+scaledWindowKernel K R (r+T):ℝ):ℂ)/2 := by
    rw [scaledModulated_cosinePacket _ hφ.continuous hφc _ _ _ hR,
      kernelTimeProfile_cosinePacket K he hc,kernelTimeProfile_cosinePacket K he hc]
    simp only [scaledWindowKernel,Complex.ofReal_add,Complex.ofReal_mul]
    ring
  have hi1 : IntegrableOn (fun T => scaledWindowKernel K R (r-T)) (Icc a b) :=
    ((scaledWindowKernel_integrable K R hR).comp_sub_left r).integrableOn
  have hi2 : IntegrableOn (fun T => scaledWindowKernel K R (r+T)) (Icc a b) := by
    have hf : Continuous (fun T => scaledWindowKernel K R (r+T)) := by
      unfold scaledWindowKernel
      fun_prop
    exact hf.continuousOn.integrableOn_compact isCompact_Icc
  rw [cosinePacket_average _ hφ.continuous hφc _ _ hR]
  simp_rw [hid]
  rw [integral_div,integral_complex_ofReal,integral_add hi1 hi2]
  have hneg : smoothedWindow K R (Icc (-b) (-a)) r=
      ∫ T in Icc a b,scaledWindowKernel K R (r+T) := by
    unfold smoothedWindow
    rw [integral_Icc_reflect]
    simp only [sub_neg_eq_add]
  rw [hneg]
  rfl

/-- Twice the positive-interval average is the time test for the full
symmetric smoothed window. -/
def symmetricWindowTimeTest (K : SchwartzMap ℝ ℝ) (R a b s : ℝ) : ℂ :=
  2*averagedTimeTest (kernelTimeProfile K) R (volume.restrict (Icc a b)) s

theorem symmetricWindowTimeTest_smooth (K : SchwartzMap ℝ ℝ) (R a b : ℝ) :
    ContDiff ℝ ∞ (symmetricWindowTimeTest K R a b) :=
  contDiff_const.mul (interval_averagedTimeTest_smooth _ (kernelTimeProfile_smooth K) R a b)

theorem symmetricWindowTimeTest_compact (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (R a b : ℝ) (hR : 0<R) :
    HasCompactSupport (symmetricWindowTimeTest K R a b) :=
  (averagedTimeTest_compactSupport _ (kernelTimeProfile_compact K hc) R hR _).mul_left

theorem symmetricWindowTimeTest_even (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (R a b : ℝ) : Function.Even (symmetricWindowTimeTest K R a b) := by
  intro s
  dsimp [symmetricWindowTimeTest]
  rw [averagedTimeTest_even _ (kernelTimeProfile_even K he)]

theorem symmetricWindowTimeTest_cosinePacket (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R a b r : ℝ) (hR : 0<R) (ha : 0<a) :
    cosinePacket (symmetricWindowTimeTest K R a b) r =
      (smoothedWindow K R (Icc a b∪Icc (-b) (-a)) r:ℂ) := by
  have heq : cosinePacket (symmetricWindowTimeTest K R a b) r =
      2*cosinePacket (averagedTimeTest (kernelTimeProfile K) R (volume.restrict (Icc a b))) r := by
    unfold cosinePacket symmetricWindowTimeTest
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with s
    ring
  rw [heq,averaged_kernelTimeProfile_cosinePacket K he hc _ _ _ _ hR,
    smoothedWindow_disjoint_union K R hR _ _ (symmetric_window_disjoint a b ha) measurableSet_Icc]
  push_cast
  ring

theorem symmetricWindowTimeTest_real (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (R a b s : ℝ) : star (symmetricWindowTimeTest K R a b s)=symmetricWindowTimeTest K R a b s := by
  unfold symmetricWindowTimeTest averagedTimeTest scaledModulatedTimeTest
  simp only [map_mul,map_ofNat,Complex.star_def]
  rw [← integral_conj]
  congr 1
  apply integral_congr_ae
  filter_upwards with T
  rw [map_mul,Complex.conj_ofReal]
  exact congrArg (fun z : ℂ => z*(Real.cos (s*T):ℂ)) (kernelTimeProfile_real K he (s/R))

/-- The propagation radius bound is uniform in the center and width. -/
theorem symmetricWindowTimeTest_uniform_support (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ B : ℝ,0<B ∧ ∀ R : ℝ,0<R → ∀ a b : ℝ,
      Function.support (symmetricWindowTimeTest K R a b)⊆Icc (-(B*R)) (B*R) := by
  obtain ⟨B,hB,hbound⟩ := (kernelTimeProfile_compact K hc).isCompact.isBounded.subset_closedBall_lt 0 (0:ℝ)
  refine ⟨B,hB,?_⟩
  intro R hR a b s hs
  have hn : kernelTimeProfile K (s/R)≠0 := by
    intro hz
    apply hs
    simp only [symmetricWindowTimeTest,averagedTimeTest,scaledModulatedTimeTest,hz,
      zero_mul,integral_zero,mul_zero]
  have h := hbound (subset_tsupport _ hn)
  have hb : |s/R|≤B := by simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero] using h
  have hp := abs_le.mp hb
  constructor
  · have h := (le_div_iff₀ hR).mp hp.1
    linarith
  · exact (div_le_iff₀ hR).mp hp.2

def windowWavePacket (N : ℕ) (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) : AutomorphicSpace N →L[ℂ] AutomorphicSpace N :=
  Wave.shiftedQuotientWavePacket N (symmetricWindowTimeTest K R a b)
    (compactSmoothWaveWeight _ (symmetricWindowTimeTest_smooth K R a b)
      (symmetricWindowTimeTest_compact K hc R a b hR))

theorem windowWavePacket_isSelfAdjoint (N : ℕ) (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) : IsSelfAdjoint (windowWavePacket N K hc R hR a b) :=
  Wave.shiftedQuotientWavePacket_isSelfAdjoint N _ _ (symmetricWindowTimeTest_real K he R a b)

theorem windowWavePacket_principal (N : ℕ) (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) (ha : 0<a) (r : ℝ) {v : AutomorphicSpace N}
    (hv : FriedrichsGraph N v (((1/4+r^2:ℝ):ℂ) • v)) :
    windowWavePacket N K hc R hR a b v =
      (smoothedWindow K R (Icc a b∪Icc (-b) (-a)) r:ℂ) • v := by
  unfold windowWavePacket
  rw [Wave.shiftedQuotientWavePacket_principal N _ _ r hv]
  change cosinePacket (symmetricWindowTimeTest K R a b) r • v=_
  rw [symmetricWindowTimeTest_cosinePacket K he hc R a b r hR ha]

/-- The square is a genuinely positive bounded operator on the entire
Hilbert space, including exceptional spectral energies. -/
theorem windowWavePacket_square_positive (N : ℕ) (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) :
    ((windowWavePacket N K hc R hR a b).comp (windowWavePacket N K hc R hR a b)).IsPositive := by
  have hs := windowWavePacket_isSelfAdjoint N K he hc R hR a b
  change (windowWavePacket N K hc R hR a b).adjoint=windowWavePacket N K hc R hR a b at hs
  have hp := ContinuousLinearMap.isPositive_adjoint_comp_self (windowWavePacket N K hc R hR a b)
  rw [hs] at hp
  exact hp

/-- The actual positive operator square has precisely the already
normalized squared-window multiplier on the principal spectrum. -/
theorem windowWavePacket_square_principal (N : ℕ) (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) (ha : 0<a) (r : ℝ) {v : AutomorphicSpace N}
    (hv : FriedrichsGraph N v (((1/4+r^2:ℝ):ℂ) • v)) :
    (windowWavePacket N K hc R hR a b).comp (windowWavePacket N K hc R hR a b) v =
      (((smoothedWindow K R (Icc a b∪Icc (-b) (-a)) r)^2:ℝ):ℂ) • v := by
  rw [ContinuousLinearMap.comp_apply,windowWavePacket_principal N K he hc R hR a b ha r hv,
    map_smul,windowWavePacket_principal N K he hc R hR a b ha r hv,smul_smul]
  congr 1
  simp only [pow_two,Complex.ofReal_mul]

theorem windowWavePacket_square_summable {ι : Type*} (N : ℕ) (hN : 0<N)
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (hcusp : ∀ i,v i∈localCuspidalSpace N hN) (e : ι → ℝ) (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (v i) ((e i:ℂ) • v i))
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) :
    Summable (fun i => ‖windowWavePacket N K hc R hR a b (v i)‖^2) :=
  cuspidal_smooth_packet_square_summable N hN v hv hcusp e he hgraph _
    (symmetricWindowTimeTest_smooth K R a b) (symmetricWindowTimeTest_compact K hc R a b hR)

theorem windowWavePacket_square_diagonal (N : ℕ) (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) (v : AutomorphicSpace N) :
    (inner ℂ v ((windowWavePacket N K hc R hR a b).comp
      (windowWavePacket N K hc R hR a b) v)).re=‖windowWavePacket N K hc R hR a b v‖^2 := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (windowWavePacket_isSelfAdjoint N K he hc R hR a b)
  have h := hs v (windowWavePacket N K hc R hR a b v)
  exact (congrArg Complex.re h.symm).trans (inner_self_eq_norm_sq (𝕜:=ℂ) _)

theorem windowWavePacket_positive_diagonal_sum {ι : Type*} (N : ℕ) (hN : 0<N)
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (hcusp : ∀ i,v i∈localCuspidalSpace N hN) (e : ι → ℝ) (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (v i) ((e i:ℂ) • v i))
    (K : SchwartzMap ℝ ℝ) (hKe : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) :
    Summable (fun i => (inner ℂ (v i) ((windowWavePacket N K hc R hR a b).comp
      (windowWavePacket N K hc R hR a b) (v i))).re) ∧
    (∑' i,(inner ℂ (v i) ((windowWavePacket N K hc R hR a b).comp
      (windowWavePacket N K hc R hR a b) (v i))).re)=
      ∑' i,‖windowWavePacket N K hc R hR a b (v i)‖^2 := by
  simp_rw [windowWavePacket_square_diagonal N K hKe hc R hR a b]
  exact ⟨windowWavePacket_square_summable N hN v hv hcusp e he hgraph K hc R hR a b,True.intro⟩

/-- A single propagation constant works for all packet centers and widths
on every actual quotient. This is the support statement for the packet P;
its positive square P*P is constructed separately above. -/
theorem windowWavePacket_uniform_propagation (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ B : ℝ,0<B ∧ ∀ (N : ℕ) (R : ℝ) (hR : 0<R) (a b : ℝ)
      (cut v w : Weighted.Cutoff N) (c d : ℝ),
      (∀ Z : UpperHalfPlane,c<(upperFunction cut.value Z).re → upperFunction v.value Z=0) →
      (∀ᵐ Z ∂quotientMeasure N,(upperFunction cut.value Z).re<d → upperFunction w.value Z=0) →
      c+|cut.gradientBound| *(B*R)<d → ∀ f : AutomorphicSpace N,
      Weighted.multiplier N w (windowWavePacket N K hc R hR a b
        (quotientLocalization N v.value v.smooth f)).val=0 := by
  obtain ⟨B,hB,hs⟩ := symmetricWindowTimeTest_uniform_support K hc
  refine ⟨B,hB,?_⟩
  intro N R hR a b cut v w c d hv hw hsep f
  exact Weighted.localized_packet_zero N cut v w c d hv hw _ (hs R hR a b) hsep f

/-- The cosine functional equation gives propagation for a packet square
without assuming a geometric kernel formula for the packet. -/
theorem compactPacket_square_annihilate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (N : ℕ) (φ : ℝ → ℂ)
    (hφ : Wave.ShiftedWaveWeight φ) (L : ℝ)
    (hs : Function.support φ⊆Icc (-L) L) (M : AutomorphicSpace N →L[ℂ] E)
    (f : AutomorphicSpace N)
    (hz : ∀ t : ℝ,|t|≤2*L → M (Wave.shiftedQuotientWave N t f)=0) :
    M (Wave.shiftedQuotientWavePacket N φ hφ (Wave.shiftedQuotientWavePacket N φ hφ f))=0 := by
  have hproduct (s t : ℝ) (hs' : φ s≠0) (ht' : φ t≠0) :
      M (Wave.shiftedQuotientWave N s (Wave.shiftedQuotientWave N t f))=0 := by
    have hsb : |s|≤L := abs_le.mpr (hs hs')
    have htb : |t|≤L := abs_le.mpr (hs ht')
    have hp : |s+t|≤2*L := (abs_add_le s t).trans (by linarith)
    have hm : |s-t|≤2*L := (abs_sub s t).trans (by linarith)
    have h := congrArg (fun A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N => M (A f))
      (Wave.shiftedQuotientWave_cosine N s t)
    simp only [add_apply,mul_apply_eq_comp,map_add,
      hz (s+t) hp,hz (s-t) hm,zero_add] at h
    have h2 : (2:ℂ) • M (Wave.shiftedQuotientWave N s (Wave.shiftedQuotientWave N t f))=0 := by
      simpa only [two_smul] using h.symm
    exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
  have hinner (s : ℝ) (hs' : φ s≠0) :
      M (Wave.shiftedQuotientWave N s (Wave.shiftedQuotientWavePacket N φ hφ f))=0 := by
    change (M.comp (Wave.shiftedQuotientWave N s)) (Wave.shiftedQuotientWavePacket N φ hφ f)=0
    rw [Wave.shiftedQuotientWavePacket_apply,
      ← (M.comp (Wave.shiftedQuotientWave N s)).integral_comp_comm
        (Wave.shiftedQuotientWave_packet_integrable N hφ f)]
    apply integral_eq_zero_of_ae
    filter_upwards with t
    simp only [ContinuousLinearMap.comp_apply,map_smul,Pi.zero_apply]
    by_cases ht' : φ t=0
    · simp only [ht',zero_smul]
    · rw [hproduct s t hs' ht',smul_zero]
  rw [Wave.shiftedQuotientWavePacket_apply,
    ← M.integral_comp_comm (Wave.shiftedQuotientWave_packet_integrable N hφ
      (Wave.shiftedQuotientWavePacket N φ hφ f))]
  apply integral_eq_zero_of_ae
  filter_upwards with s
  simp only [map_smul,Pi.zero_apply]
  by_cases hs' : φ s=0
  · rw [hs',zero_smul]
  · rw [hinner s hs',smul_zero]

/-- The actual positive squared-window operator has propagation at most
2*B*R, uniformly in its spectral center and width. -/
theorem windowWavePacket_square_uniform_propagation (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ B : ℝ,0<B ∧ ∀ (N : ℕ) (R : ℝ) (hR : 0<R) (a b : ℝ)
      (cut v w : Weighted.Cutoff N) (c d : ℝ),
      (∀ Z : UpperHalfPlane,c<(upperFunction cut.value Z).re → upperFunction v.value Z=0) →
      (∀ᵐ Z ∂quotientMeasure N,(upperFunction cut.value Z).re<d → upperFunction w.value Z=0) →
      c+|cut.gradientBound| * (2*(B*R))<d → ∀ f : AutomorphicSpace N,
      Weighted.multiplier N w ((windowWavePacket N K hc R hR a b).comp
        (windowWavePacket N K hc R hR a b)
        (quotientLocalization N v.value v.smooth f)).val=0 := by
  obtain ⟨B,hB,hs⟩ := symmetricWindowTimeTest_uniform_support K hc
  refine ⟨B,hB,?_⟩
  intro N R hR a b cut v w c d hv hw hsep f
  apply compactPacket_square_annihilate N (symmetricWindowTimeTest K R a b) _ (B*R)
    (hs R hR a b) ((Weighted.multiplier N w).comp (AutomorphicSpace N).subtypeL)
    (quotientLocalization N v.value v.smooth f)
  intro t ht
  apply Weighted.localized_wave_zero N cut v w c d hv hw t _ f
  have hb := mul_le_mul_of_nonneg_left ht (abs_nonneg cut.gradientBound)
  linarith

#print axioms compactPacket_square_annihilate
#print axioms windowWavePacket_square_uniform_propagation

#print axioms windowWavePacket_square_diagonal
#print axioms windowWavePacket_positive_diagonal_sum
#print axioms windowWavePacket_uniform_propagation

#print axioms symmetricWindowTimeTest_real
#print axioms symmetricWindowTimeTest_uniform_support
#print axioms windowWavePacket_isSelfAdjoint
#print axioms windowWavePacket_principal
#print axioms windowWavePacket_square_positive
#print axioms windowWavePacket_square_principal
#print axioms windowWavePacket_square_summable

#print axioms integral_Icc_reflect
#print axioms averaged_kernelTimeProfile_cosinePacket
#print axioms symmetricWindowTimeTest_smooth
#print axioms symmetricWindowTimeTest_compact
#print axioms symmetricWindowTimeTest_even
#print axioms symmetricWindowTimeTest_cosinePacket

#print axioms kernelTimeProfile_smooth
#print axioms kernelTimeProfile_compact
#print axioms kernelTimeProfile_even
#print axioms kernelTimeProfile_real
#print axioms kernelTimeProfile_cosinePacket

end QuantitativeMaass
