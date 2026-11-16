module

public import QuantitativeMaassLVParityAccuracyV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace ENNReal SchwartzMap

namespace QuantitativeMaass

/-- Each parity piece of the positive LV quadratic form lies between zero
and the full quadratic form, using its actual parity commutation. -/
theorem actualLVFilter_parity_quadratic_bounds (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1) (d : ℕ)
    (σ : ℝ) (hσ : σ^2=1) (v : AutomorphicSpace N) :
    0≤(inner ℂ (actualLVFilter N p hN hpN a b hab d (parityProjection N σ v)) (parityProjection N σ v)).re ∧
    (inner ℂ (actualLVFilter N p hN hpN a b hab d (parityProjection N σ v)) (parityProjection N σ v)).re≤
      (inner ℂ (actualLVFilter N p hN hpN a b hab d v) v).re := by
  have hp (x : AutomorphicSpace N) : 0≤(inner ℂ (actualLVFilter N p hN hpN a b hab d x) x).re :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp (actualLVFilter_order N p hN hpN a b hab d).1).re_inner_nonneg_left x
  refine ⟨hp _,?_⟩
  have hh := congrArg Complex.re (actualLVFilter_parity_split N p hN hpN hNp a b hab d σ hσ v)
  rw [Complex.add_re] at hh
  linarith [hp (parityProjection N (-σ) v)]

/-- The actual original-time parity LV kernel is integrable on the entire
quotient. Positivity and exact splitting dominate it by the proved full kernel. -/
theorem timeWavePacket_parity_actualLV_kernel_integrable
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1) (d : ℕ) (σ : ℝ) (hσ : σ^2=1)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    Integrable (fun x => (inner ℂ
      (actualLVFilter N p hN hpN a b hab d (parityProjection N σ (timeAbelColumn N f hc he R hR hs x)))
      (parityProjection N σ (timeAbelColumn N f hc he R hR hs x))).re) (quotientMeasure N) := by
  have hi := timeWavePacket_actualLV_kernel_integrable N p hN hpN hNp hpres a b hab d f hc he hr R hR hs
  have ht : Continuous (timeAbelColumn N f hc he R hR hs) := oneSidedAbelColumn_continuous N _ _ _ _ _
  have hcol := (parityProjection N σ).continuous.comp ht
  apply hi.mono' ((Complex.continuous_re.comp
    (((actualLVFilter N p hN hpN a b hab d).continuous.comp hcol).inner hcol)).aestronglyMeasurable)
  filter_upwards with x
  dsimp only [Function.comp_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg (actualLVFilter_parity_quadratic_bounds N p hN hpN hNp a b hab d σ hσ _).1]
  exact (actualLVFilter_parity_quadratic_bounds N p hN hpN hNp a b hab d σ hσ _).2

/-- Exact parity trace on a genuine cusp basis. The basis need not diagonalize
Hecke or parity; both actual operators remain inside the quadratic coefficient. -/
theorem timeWavePacket_parity_actualLV_trace_eq_cusp_basis {κ : Type*}
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1) (d : ℕ) (σ : ℝ)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN))
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    let L := actualLVFilter N p hN hpN a b hab d
    let P := parityProjection N σ
    let A := Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f (f.smooth ⊤) hc)
    (∫⁻ x,ENNReal.ofReal ((inner ℂ (L (P (timeAbelColumn N f hc he R hR hs x)))
      (P (timeAbelColumn N f hc he R hR hs x))).re) ∂quotientMeasure N)=
      ∑' j,ENNReal.ofReal ((inner ℂ (L (P (A (basis j:AutomorphicSpace N))))
        (P (A (basis j:AutomorphicSpace N)))).re) := by
  obtain ⟨ι,hι,⟨B⟩⟩ := exists_countable_automorphic_basis N
  have : Countable ι := hι
  let L := actualLVFilter N p hN hpN a b hab d
  let P := parityProjection N σ
  have hpos : 0≤P*L*P := by
    have hh := star_left_conjugate_nonneg (actualLVFilter_order N p hN hpN a b hab d).1 P
    change 0≤star P*L*P at hh
    rwa [(parityProjection_selfAdjoint N σ).star_eq] at hh
  have hh := positive_smoothed_trace_two_bases (localCuspidalSpace N hN) B basis
    (Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f (f.smooth ⊤) hc))
    (P*L*P) (Wave.shiftedQuotientWavePacket_isSelfAdjoint N f _ hr) hpos
    (fun x hx => shiftedQuotientWavePacket_mem_localCuspidalSpace N hN _ _ x hx)
    (fun x => parityProjection_mem_localCuspidalSpace N hN σ _
      (actualLVFilter_mem_localCuspidalSpace N p hN hpN hNp hpres a b hab d _))
  dsimp only
  rw [← timeWavePacket_parity_actualLV_trace N p hN hpN a b hab d B σ f hc he hr R hR hs]
  simpa only [P,parityCompression_quadratic] using hh

/-- Exact scalar parity LV spectrum; only the energy basis is required, and
parity remains in the genuine bounded quadratic coefficient. -/
theorem timeWavePacket_parity_actualLV_trace_eq_weighted_spectrum {κ : Type*}
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1) (d : ℕ) (σ : ℝ)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (henergy : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (basis j:AutomorphicSpace N) ((e j:ℂ) • (basis j:AutomorphicSpace N)))
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    (∫⁻ x,ENNReal.ofReal ((inner ℂ
      (actualLVFilter N p hN hpN a b hab d (parityProjection N σ (timeAbelColumn N f hc he R hR hs x)))
      (parityProjection N σ (timeAbelColumn N f hc he R hR hs x))).re) ∂quotientMeasure N)=
      ∑' j,ENNReal.ofReal (‖smoothPacketMultiplier f (e j)‖^2 *
        (inner ℂ (actualLVFilter N p hN hpN a b hab d (parityProjection N σ (basis j:AutomorphicSpace N)))
          (parityProjection N σ (basis j:AutomorphicSpace N))).re) := by
  rw [timeWavePacket_parity_actualLV_trace_eq_cusp_basis N p hN hpN hNp hpres a b hab d σ basis f hc he hr R hR hs]
  apply tsum_congr
  intro j
  rw [Wave.shiftedQuotientWavePacket_eigen N f _ (henergy j) (hgraph j),map_smul,
    positive_quadratic_smul _ (actualLVFilter_order N p hN hpN a b hab d).1]
  rfl

/-- Ordinary convergent parity LV trace, including exceptional spectral energies. -/
theorem timeWavePacket_parity_actualLV_real_trace {κ : Type*}
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a c : ℤ) (hac : (p:ℤ)*a+(N:ℤ)*c=1) (d : ℕ) (σ : ℝ) (hσ : σ^2=1)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (henergy : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (basis j:AutomorphicSpace N) ((e j:ℂ) • (basis j:AutomorphicSpace N)))
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    HasSum (fun j => ‖smoothPacketMultiplier f (e j)‖^2 *
      (inner ℂ (actualLVFilter N p hN hpN a c hac d (parityProjection N σ (basis j:AutomorphicSpace N)))
        (parityProjection N σ (basis j:AutomorphicSpace N))).re)
      (∫ x,(inner ℂ
        (actualLVFilter N p hN hpN a c hac d (parityProjection N σ (timeAbelColumn N f hc he R hR hs x)))
        (parityProjection N σ (timeAbelColumn N f hc he R hR hs x))).re ∂quotientMeasure N) := by
  let L := actualLVFilter N p hN hpN a c hac d
  let q := fun x => (inner ℂ (L (parityProjection N σ (timeAbelColumn N f hc he R hR hs x)))
    (parityProjection N σ (timeAbelColumn N f hc he R hR hs x))).re
  let w := fun j => ‖smoothPacketMultiplier f (e j)‖^2 *
    (inner ℂ (L (parityProjection N σ (basis j:AutomorphicSpace N))) (parityProjection N σ (basis j:AutomorphicSpace N))).re
  have hp (v : AutomorphicSpace N) : 0≤(inner ℂ (L v) v).re :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp (actualLVFilter_order N p hN hpN a c hac d).1).re_inner_nonneg_left v
  have hw (j : κ) : 0≤w j := mul_nonneg (sq_nonneg _) (hp _)
  have hq : 0≤ᵐ[quotientMeasure N] q := Eventually.of_forall (fun x => hp _)
  have hint : Integrable q (quotientMeasure N) :=
    timeWavePacket_parity_actualLV_kernel_integrable N p hN hpN hNp hpres a c hac d σ hσ f hc he hr R hR hs
  have henn : (∫⁻ x,ENNReal.ofReal (q x) ∂quotientMeasure N)=∑' j,ENNReal.ofReal (w j) :=
    timeWavePacket_parity_actualLV_trace_eq_weighted_spectrum N p hN hpN hNp hpres a c hac d σ basis e henergy hgraph f hc he hr R hR hs
  have hfin : (∑' j,ENNReal.ofReal (w j))≠⊤ := by
    rw [← henn]
    exact (lintegral_ofReal_ne_top_iff_integrable hint.aestronglyMeasurable hq).mpr hint
  have hsum : Summable w := (ENNReal.summable_toReal hfin).congr (fun j => ENNReal.toReal_ofReal (hw j))
  have heq : (∫ x,q x ∂quotientMeasure N)=∑' j,w j := by
    rw [integral_eq_lintegral_of_nonneg_ae hq hint.aestronglyMeasurable,henn,
      ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    exact tsum_congr (fun j => ENNReal.toReal_ofReal (hw j))
  change HasSum w (∫ x,q x ∂quotientMeasure N)
  rw [heq]
  exact hsum.hasSum


#print axioms actualLVFilter_parity_quadratic_bounds
#print axioms timeWavePacket_parity_actualLV_kernel_integrable
#print axioms timeWavePacket_parity_actualLV_trace_eq_cusp_basis

#print axioms timeWavePacket_parity_actualLV_trace_eq_weighted_spectrum
#print axioms timeWavePacket_parity_actualLV_real_trace

end QuantitativeMaass
