module

public import QuantitativeMaassWindowTimeRealizationV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff

namespace QuantitativeMaass

universe u

/-- Averaging costs only the mass of the parameter measure, uniformly in its location. -/
theorem averagedTimeTest_norm_le (φ : ℝ → ℂ) (R s : ℝ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ‖averagedTimeTest φ R μ s‖ ≤ ‖φ (s/R)‖ * μ.real univ := by
  apply norm_integral_le_of_norm_le_const
  filter_upwards with T
  dsimp [scaledModulatedTimeTest]
  rw [norm_mul]
  have hc : ‖(Real.cos (s*T):ℂ)‖≤1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one (s*T)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hc (norm_nonneg (φ (s/R)))

theorem symmetricWindowTimeTest_norm_le (K : SchwartzMap ℝ ℝ)
    (R a b s : ℝ) (hab : a≤b) :
    ‖symmetricWindowTimeTest K R a b s‖ ≤ 2*(b-a)*‖kernelTimeProfile K (s/R)‖ := by
  have h := averagedTimeTest_norm_le (kernelTimeProfile K) R s (volume.restrict (Icc a b))
  rw [measureReal_restrict_apply_univ,Real.volume_real_Icc_of_le hab] at h
  simp only [symmetricWindowTimeTest,norm_mul]
  norm_num only [Complex.norm_ofNat]
  nlinarith

/-- Compact time support converts the exceptional spectral weight to one fixed constant. -/
theorem compact_time_weight_bound (φ : ℝ → ℂ) (hi : Integrable φ)
    (L : ℝ) (hL : 0≤L) (hs : Function.support φ⊆Icc (-L) L) :
    (∫ s,‖φ s‖*Real.cosh (|s|/2)) ≤ (∫ s,‖φ s‖)*Real.cosh (L/2) := by
  have hw := Wave.shiftedWaveWeight_of_support hi hL hs
  calc
    _ ≤ ∫ s,‖φ s‖*Real.cosh (L/2) := by
      apply integral_mono hw.2 (hi.norm.mul_const _)
      intro s
      by_cases hz : φ s=0
      · simp [hz]
      · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply Real.cosh_le_cosh.mpr
        rw [abs_of_nonneg (div_nonneg (abs_nonneg s) (by norm_num)),
          abs_of_nonneg (div_nonneg hL (by norm_num))]
        exact div_le_div_of_nonneg_right (abs_le.mpr (hs hz)) (by norm_num)
    _ = _ := integral_mul_const _ _

theorem symmetricWindowTimeTest_l1_bound (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) (hab : a≤b) :
    (∫ s,‖symmetricWindowTimeTest K R a b s‖) ≤
      2*(b-a)*R*(∫ s,‖kernelTimeProfile K s‖) := by
  have hi : Integrable (kernelTimeProfile K) := (kernelTimeProfile_smooth K).continuous.integrable_of_hasCompactSupport
    (kernelTimeProfile_compact K hc)
  have hir : Integrable (fun s => kernelTimeProfile K (s/R)) :=
    (integrable_comp_div_iff _ hR.ne').mpr hi
  have ht : Integrable (symmetricWindowTimeTest K R a b) := (symmetricWindowTimeTest_smooth K R a b).continuous.integrable_of_hasCompactSupport
    (symmetricWindowTimeTest_compact K hc R a b hR)
  calc
    _ ≤ ∫ s,2*(b-a)*‖kernelTimeProfile K (s/R)‖ :=
      integral_mono ht.norm (hir.norm.const_mul _) (fun s => symmetricWindowTimeTest_norm_le K R a b s hab)
    _ = _ := by
      rw [integral_const_mul,Measure.integral_comp_div (fun s => ‖kernelTimeProfile K s‖) R,
        abs_of_pos hR,smul_eq_mul]
      ring

/-- One pair of constants works for every level, center, width and positive dilation. -/
theorem windowWavePacket_uniform_norm (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ B C : ℝ,0<B ∧ 0<C ∧ ∀ (N : ℕ) (R : ℝ) (hR : 0<R) (a b : ℝ),a≤b →
      ‖windowWavePacket N K hc R hR a b‖ ≤ C*(b-a)*R*Real.cosh (B*R/2) := by
  obtain ⟨B,hB,hs⟩ := symmetricWindowTimeTest_uniform_support K hc
  let M : ℝ := ∫ s,‖kernelTimeProfile K s‖
  have hM : 0≤M := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨B,2*M+1,hB,by linarith,?_⟩
  intro N R hR a b hab
  have ht : Integrable (symmetricWindowTimeTest K R a b) := (symmetricWindowTimeTest_smooth K R a b).continuous.integrable_of_hasCompactSupport
    (symmetricWindowTimeTest_compact K hc R a b hR)
  have hmass := symmetricWindowTimeTest_l1_bound K hc R hR a b hab
  have hcos : 0≤Real.cosh (B*R/2) := (Real.cosh_pos _).le
  calc
    _ ≤ ∫ s,‖symmetricWindowTimeTest K R a b s‖*Real.cosh (|s|/2) :=
      Wave.shiftedQuotientWavePacket_norm N _ _
    _ ≤ (∫ s,‖symmetricWindowTimeTest K R a b s‖)*Real.cosh (B*R/2) :=
      compact_time_weight_bound _ ht (B*R) (mul_nonneg hB.le hR.le) (hs R hR a b)
    _ ≤ (2*(b-a)*R*M)*Real.cosh (B*R/2) := mul_le_mul_of_nonneg_right hmass hcos
    _ ≤ (2*M+1)*(b-a)*R*Real.cosh (B*R/2) := by
      have hprod : 0≤(b-a)*R*Real.cosh (B*R/2) :=
        mul_nonneg (mul_nonneg (sub_nonneg.mpr hab) hR.le) hcos
      nlinarith

/-- The square norm grows at most exponentially in the time radius. -/
theorem windowWavePacket_uniform_square_norm (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ B C : ℝ,0<B ∧ 0<C ∧ ∀ (N : ℕ) (R : ℝ) (hR : 0<R) (a b : ℝ),a≤b →
      ‖windowWavePacket N K hc R hR a b‖^2 ≤ C*(b-a)^2*R^2*Real.exp (B*R) := by
  obtain ⟨B,C,hB,hC,hbound⟩ := windowWavePacket_uniform_norm K hc
  refine ⟨B,C^2,hB,sq_pos_of_pos hC,?_⟩
  intro N R hR a b hab
  have hx : 0≤B*R/2 := div_nonneg (mul_nonneg hB.le hR.le) (by norm_num)
  have hexp : Real.exp (-(B*R/2))≤Real.exp (B*R/2) := Real.exp_le_exp.mpr (by linarith)
  have hcos : Real.cosh (B*R/2)≤Real.exp (B*R/2) := by rw [Real.cosh_eq]; linarith
  have hnorm := (hbound N R hR a b hab).trans
    (mul_le_mul_of_nonneg_left hcos (mul_nonneg (mul_nonneg hC.le (sub_nonneg.mpr hab)) hR.le))
  have hsq := pow_le_pow_left₀ (norm_nonneg (windowWavePacket N K hc R hR a b)) hnorm 2
  have heq : (Real.exp (B*R/2))^2=Real.exp (B*R) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ (C*(b-a)*R*Real.exp (B*R/2))^2 := hsq
    _ = _ := by simp only [mul_pow,heq]

/-- Uniform bound for the entire exceptional-energy contribution. Finiteness
is deduced from the proved cuspidal counting theorem, not supplied as a premise. -/
theorem windowWavePacket_exceptional_sum_bound (N : ℕ) (hN : 0<N)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ B C : ℝ,0<B ∧ 0<C ∧ ∀ (ι : Type u) (v : ι → AutomorphicSpace N),
      Orthonormal ℂ v → (∀ i,v i∈localCuspidalSpace N hN) →
      ∀ e : ι → ℝ,(∀ i,0≤e i) →
      (∀ i,FriedrichsGraph N (v i) ((e i:ℂ) • v i)) →
      ∀ (R : ℝ) (hR : 0<R) (a b : ℝ),a≤b →
        {i | e i≤1/4}.Finite ∧
        (∑' i : {i // e i≤1/4}, ‖windowWavePacket N K hc R hR a b (v i.val)‖^2) ≤
          C*(b-a)^2*R^2*Real.exp (B*R) := by
  obtain ⟨B,C,hB,hC,hpacket⟩ := windowWavePacket_uniform_square_norm K hc
  obtain ⟨D,hD,hcount⟩ := cuspidal_spectral_band_polynomial N hN
  refine ⟨B,D*(1/4+1)^6*C,hB,by positivity,?_⟩
  intro ι v hv hcusp e he hgraph R hR a b hab
  obtain ⟨hf,hn⟩ := hcount ι v hv hcusp e he hgraph (1/4) (by norm_num)
  refine ⟨hf,?_⟩
  let J := {i // e i≤1/4}
  have : Finite J := Set.finite_coe_iff.mpr hf
  let : Fintype J := Fintype.ofFinite J
  let Q := C*(b-a)^2*R^2*Real.exp (B*R)
  have hQ : 0≤Q := mul_nonneg (mul_nonneg (mul_nonneg hC.le (sq_nonneg _))
    (sq_nonneg _)) (Real.exp_pos _).le
  have hp (i : J) : ‖windowWavePacket N K hc R hR a b (v i.val)‖^2≤Q := by
    have hop := (windowWavePacket N K hc R hR a b).le_opNorm (v i.val)
    rw [hv.norm_eq_one i.val,mul_one] at hop
    exact (pow_le_pow_left₀ (norm_nonneg _) hop 2).trans (hpacket N R hR a b hab)
  calc
    _ = ∑ i : J,‖windowWavePacket N K hc R hR a b (v i.val)‖^2 := tsum_fintype _
    _ ≤ ∑ _i : J,Q := Finset.sum_le_sum (fun i _ => hp i)
    _ = (Nat.card J:ℝ)*Q := by simp [Nat.card_eq_fintype_card]
    _ ≤ (D*(1/4+1)^6)*Q := mul_le_mul_of_nonneg_right hn hQ
    _ = _ := by dsimp [Q]; ring

/-- For windows of width at most one, the actual positive-square diagonal
on all exceptional eigenvalues is bounded independently of the center. -/
theorem windowWavePacket_exceptional_diagonal_bound (N : ℕ) (hN : 0<N)
    (K : SchwartzMap ℝ ℝ) (hKe : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ B C : ℝ,0<B ∧ 0<C ∧ ∀ (ι : Type u) (v : ι → AutomorphicSpace N),
      Orthonormal ℂ v → (∀ i,v i∈localCuspidalSpace N hN) →
      ∀ e : ι → ℝ,(∀ i,0≤e i) →
      (∀ i,FriedrichsGraph N (v i) ((e i:ℂ) • v i)) →
      ∀ (R : ℝ) (hR : 0<R) (a b : ℝ),a≤b → b-a≤1 →
        (∑' i : {i // e i≤1/4}, (inner ℂ (v i.val)
          ((windowWavePacket N K hc R hR a b).comp
            (windowWavePacket N K hc R hR a b) (v i.val))).re) ≤
          C*R^2*Real.exp (B*R) := by
  obtain ⟨B,C,hB,hC,hbound⟩ := windowWavePacket_exceptional_sum_bound N hN K hc
  refine ⟨B,C,hB,hC,?_⟩
  intro ι v hv hcusp e he hgraph R hR a b hab hw
  simp_rw [windowWavePacket_square_diagonal N K hKe hc R hR a b]
  have h := (hbound ι v hv hcusp e he hgraph R hR a b hab).2
  have hwidth : (b-a)^2≤1 := by nlinarith [sub_nonneg.mpr hab]
  have hnon : 0≤C*R^2*Real.exp (B*R) :=
    mul_nonneg (mul_nonneg hC.le (sq_nonneg _)) (Real.exp_pos _).le
  calc
    _ ≤ C*(b-a)^2*R^2*Real.exp (B*R) := h
    _ = (b-a)^2*(C*R^2*Real.exp (B*R)) := by ring
    _ ≤ C*R^2*Real.exp (B*R) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hwidth hnon

#print axioms windowWavePacket_exceptional_diagonal_bound
#print axioms windowWavePacket_uniform_square_norm
#print axioms windowWavePacket_exceptional_sum_bound
#print axioms averagedTimeTest_norm_le
#print axioms symmetricWindowTimeTest_norm_le
#print axioms compact_time_weight_bound
#print axioms symmetricWindowTimeTest_l1_bound
#print axioms windowWavePacket_uniform_norm

end QuantitativeMaass
