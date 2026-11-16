module

public import QuantitativeMaassParityCuspidalTraceV1
public import QuantitativeMaassLVTraceTheoremV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace ENNReal SchwartzMap

namespace QuantitativeMaass

/-- Original compact time packets have a finite full-space cusp-projected
energy. The actual cusp energy basis and its polynomial count are constructed
by previously checked theorems, rather than assumed here. -/
theorem timeWavePacket_cuspidal_energy_finite {ι : Type*}
    (N : ℕ) [NeZero N] (hN : 0<N) (b : HilbertBasis ι ℂ (AutomorphicSpace N))
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (hr : ∀ t,star (f t)=f t) :
    (∑' i,ENNReal.ofReal (‖localCuspidalProjection N hN
      (Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f (f.smooth ⊤) hc) (b i))‖^2))
      <(∞:ℝ≥0∞) := by
  obtain ⟨κ,c,e,he,hgraph,_⟩ := QuantitativeArithmeticMaassCuspBand.exists_cuspidal_energy_basis N hN
  have hA := Wave.shiftedQuotientWavePacket_isSelfAdjoint N f
    (compactSmoothWaveWeight f (f.smooth ⊤) hc) hr
  have ho : Orthonormal ℂ (fun j => (c j:AutomorphicSpace N)) :=
    c.orthonormal.comp_linearIsometry (localCuspidalSpace N hN).subtypeₗᵢ
  have hsum := cuspidal_smooth_packet_square_summable N hN (fun j => (c j:AutomorphicSpace N))
    ho (fun j => (c j).property) e he hgraph f (f.smooth ⊤) hc
  change (∑' i,ENNReal.ofReal (‖(localCuspidalSpace N hN).starProjection
    (Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f (f.smooth ⊤) hc) (b i))‖^2))<_
  rw [projected_energy_two_bases (localCuspidalSpace N hN) b c,hA.adjoint_eq]
  exact hsum.tsum_ofReal_lt_top

/-- The ordinary original-time LV kernel is integrable, including time
zero. This discharges trace finiteness without a globally smooth radial lift. -/
theorem timeWavePacket_actualLV_kernel_integrable
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a c : ℤ) (hac : (p:ℤ)*a+(N:ℤ)*c=1) (d : ℕ)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    Integrable (fun x => (inner ℂ
      (actualLVFilter N p hN hpN a c hac d (timeAbelColumn N f hc he R hR hs x))
      (timeAbelColumn N f hc he R hR hs x)).re) (quotientMeasure N) := by
  obtain ⟨ι,hι,⟨b⟩⟩ := exists_countable_automorphic_basis N
  have : Countable ι := hι
  have hcont : Continuous (timeAbelColumn N f hc he R hR hs) :=
    oneSidedAbelColumn_continuous N _ _ _ _ _
  have hm : AEStronglyMeasurable (fun x => (inner ℂ
      (actualLVFilter N p hN hpN a c hac d (timeAbelColumn N f hc he R hR hs x))
      (timeAbelColumn N f hc he R hR hs x)).re) (quotientMeasure N) := by
    have hq : Continuous (fun x => inner ℂ
        (actualLVFilter N p hN hpN a c hac d (timeAbelColumn N f hc he R hR hs x))
        (timeAbelColumn N f hc he R hR hs x)) :=
      ((actualLVFilter N p hN hpN a c hac d).continuous.comp hcont).inner hcont
    exact (Complex.continuous_re.comp hq).aestronglyMeasurable
  apply (lintegral_ofReal_ne_top_iff_integrable hm
    (Eventually.of_forall (fun x => (ContinuousLinearMap.nonneg_iff_isPositive.mp
      (actualLVFilter_order N p hN hpN a c hac d).1).re_inner_nonneg_left _))).mp
  exact ((timeWavePacket_actualLV_trace_le_cuspidal N f hc he hr R hR hs b p hN hpN hNp hpres a c hac d).trans_lt
    (timeWavePacket_cuspidal_energy_finite N hN b f hc hr)).ne

/-- The actual original-time LV kernel equals a cusp-basis trace with no
trace formula assumption. The cusp basis need not diagonalize the Hecke operator. -/
theorem timeWavePacket_actualLV_trace_eq_cusp_basis {κ : Type*}
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a c : ℤ) (hac : (p:ℤ)*a+(N:ℤ)*c=1) (d : ℕ)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN))
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    let L := actualLVFilter N p hN hpN a c hac d
    let A := Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f (f.smooth ⊤) hc)
    (∫⁻ x,ENNReal.ofReal ((inner ℂ (L (timeAbelColumn N f hc he R hR hs x))
      (timeAbelColumn N f hc he R hR hs x)).re) ∂quotientMeasure N)=
      ∑' j,ENNReal.ofReal ((inner ℂ (L (A (basis j:AutomorphicSpace N)))
        (A (basis j:AutomorphicSpace N))).re) := by
  obtain ⟨ι,hι,⟨b⟩⟩ := exists_countable_automorphic_basis N
  have : Countable ι := hι
  dsimp only
  rw [← timeWavePacket_positive_kernel_trace N f hc he hr R hR hs b
    (actualLVFilter N p hN hpN a c hac d) (actualLVFilter_order N p hN hpN a c hac d).1]
  apply positive_smoothed_trace_two_bases (localCuspidalSpace N hN) b basis
  · exact Wave.shiftedQuotientWavePacket_isSelfAdjoint N f _ hr
  · exact (actualLVFilter_order N p hN hpN a c hac d).1
  · intro x hx
    exact shiftedQuotientWavePacket_mem_localCuspidalSpace N hN _ _ x hx
  · exact actualLVFilter_mem_localCuspidalSpace N p hN hpN hNp hpres a c hac d

/-- Exact scalar spectral trace for the original time test, including the
exceptional energies represented by smoothPacketMultiplier. -/
theorem timeWavePacket_actualLV_trace_eq_weighted_spectrum {κ : Type*}
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a c : ℤ) (hac : (p:ℤ)*a+(N:ℤ)*c=1) (d : ℕ)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (henergy : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (basis j:AutomorphicSpace N) ((e j:ℂ) • (basis j:AutomorphicSpace N)))
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    (∫⁻ x,ENNReal.ofReal ((inner ℂ
      (actualLVFilter N p hN hpN a c hac d (timeAbelColumn N f hc he R hR hs x))
      (timeAbelColumn N f hc he R hR hs x)).re) ∂quotientMeasure N)=
      ∑' j,ENNReal.ofReal (‖smoothPacketMultiplier f (e j)‖^2 *
        (inner ℂ (actualLVFilter N p hN hpN a c hac d (basis j:AutomorphicSpace N))
          (basis j:AutomorphicSpace N)).re) := by
  rw [timeWavePacket_actualLV_trace_eq_cusp_basis N p hN hpN hNp hpres a c hac d basis f hc he hr R hR hs]
  apply tsum_congr
  intro j
  rw [Wave.shiftedQuotientWavePacket_eigen N f _ (henergy j) (hgraph j),
    positive_quadratic_smul _ (actualLVFilter_order N p hN hpN a c hac d).1]
  rfl

/-- Ordinary absolutely convergent scalar trace, not merely an extended-real
identity. All exceptional energy contributions remain in the actual multiplier. -/
theorem timeWavePacket_actualLV_real_trace {κ : Type*}
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a c : ℤ) (hac : (p:ℤ)*a+(N:ℤ)*c=1) (d : ℕ)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (henergy : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (basis j:AutomorphicSpace N) ((e j:ℂ) • (basis j:AutomorphicSpace N)))
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    HasSum (fun j => ‖smoothPacketMultiplier f (e j)‖^2 *
      (inner ℂ (actualLVFilter N p hN hpN a c hac d (basis j:AutomorphicSpace N))
        (basis j:AutomorphicSpace N)).re)
      (∫ x,(inner ℂ
        (actualLVFilter N p hN hpN a c hac d (timeAbelColumn N f hc he R hR hs x))
        (timeAbelColumn N f hc he R hR hs x)).re ∂quotientMeasure N) := by
  let L := actualLVFilter N p hN hpN a c hac d
  let q := fun x => (inner ℂ (L (timeAbelColumn N f hc he R hR hs x))
    (timeAbelColumn N f hc he R hR hs x)).re
  let w := fun j => ‖smoothPacketMultiplier f (e j)‖^2 *
    (inner ℂ (L (basis j:AutomorphicSpace N)) (basis j:AutomorphicSpace N)).re
  have hp (v : AutomorphicSpace N) : 0≤(inner ℂ (L v) v).re :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp (actualLVFilter_order N p hN hpN a c hac d).1).re_inner_nonneg_left v
  have hw (j : κ) : 0≤w j := mul_nonneg (sq_nonneg _) (hp _)
  have hq : 0≤ᵐ[quotientMeasure N] q := Eventually.of_forall (fun x => hp _)
  have hint : Integrable q (quotientMeasure N) :=
    timeWavePacket_actualLV_kernel_integrable N p hN hpN hNp hpres a c hac d f hc he hr R hR hs
  have henn : (∫⁻ x,ENNReal.ofReal (q x) ∂quotientMeasure N)=∑' j,ENNReal.ofReal (w j) :=
    timeWavePacket_actualLV_trace_eq_weighted_spectrum N p hN hpN hNp hpres a c hac d basis e henergy hgraph f hc he hr R hR hs
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

/-- A genuine countable cusp energy basis is constructed internally and
realizes the convergent original-time LV trace. No eigenbasis or trace premise. -/
theorem exists_timeWavePacket_actualLV_spectral_trace
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a c : ℤ) (hac : (p:ℤ)*a+(N:ℤ)*c=1) (d : ℕ)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    ∃ (κ : Type) (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ),
      Countable κ ∧ (∀ j,0≤e j) ∧
      (∀ j,FriedrichsGraph N (basis j:AutomorphicSpace N) ((e j:ℂ) • (basis j:AutomorphicSpace N))) ∧
      HasSum (fun j => ‖smoothPacketMultiplier f (e j)‖^2 *
        (inner ℂ (actualLVFilter N p hN hpN a c hac d (basis j:AutomorphicSpace N))
          (basis j:AutomorphicSpace N)).re)
        (∫ x,(inner ℂ
          (actualLVFilter N p hN hpN a c hac d (timeAbelColumn N f hc he R hR hs x))
          (timeAbelColumn N f hc he R hR hs x)).re ∂quotientMeasure N) := by
  obtain ⟨κ,basis,e,henergy,hgraph,_⟩ := QuantitativeArithmeticMaassCuspBand.exists_cuspidal_energy_basis N hN
  exact ⟨κ,basis,e,cuspidal_basis_countable N hN basis,henergy,hgraph,
    timeWavePacket_actualLV_real_trace N p hN hpN hNp hpres a c hac d basis e henergy hgraph f hc he hr R hR hs⟩

#print axioms timeWavePacket_actualLV_real_trace
#print axioms exists_timeWavePacket_actualLV_spectral_trace

#print axioms timeWavePacket_cuspidal_energy_finite
#print axioms timeWavePacket_actualLV_kernel_integrable
#print axioms timeWavePacket_actualLV_trace_eq_cusp_basis
#print axioms timeWavePacket_actualLV_trace_eq_weighted_spectrum

end QuantitativeMaass
