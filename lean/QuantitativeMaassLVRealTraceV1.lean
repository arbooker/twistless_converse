module

public import QuantitativeMaassLVSpectralTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped ENNReal ContDiff InnerProductSpace

namespace QuantitativeMaass

/-- Transfer measurable filtered square norms to a positive quadratic kernel. -/
theorem positive_kernel_measurable_of_filtered {H X : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [MeasurableSpace X] (μ : Measure X) (D : H →L[ℂ] H) (hD : 0≤D)
    (row : X → H)
    (hm : ∀ B : H →L[ℂ] H,AEStronglyMeasurable (fun x => ‖B.adjoint (row x)‖^2) μ) :
    AEStronglyMeasurable (fun x => (inner ℂ (D (row x)) (row x)).re) μ := by
  have hroot : IsSelfAdjoint (CFC.sqrt D) :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg D)).isSelfAdjoint
  simpa only [hroot.adjoint_eq,positive_sqrt_norm_square D hD] using hm (CFC.sqrt D)

/-- Measurability of the geometric positive quadratic kernel follows from
its local pretrace expansion. No regularity of the Hilbert-valued kernel row
and no global trace-finiteness premise are assumed. -/
theorem cosh_positive_kernel_aestronglyMeasurable {ι : Type*} [Countable ι]
    (N : ℕ) [NeZero N] (b : HilbertBasis ι ℂ (AutomorphicSpace N))
    (D : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) (hD : 0≤D)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    AEStronglyMeasurable (fun x => (inner ℂ
      (D (poincareSeedVector N (radialSeed (abelProfile F) (abelProfile_smooth F hF hc)
          x R hR (abelProfile_support F _ hs))))
      (poincareSeedVector N (radialSeed (abelProfile F) (abelProfile_smooth F hF hc)
        x R hR (abelProfile_support F _ hs)))).re) (quotientMeasure N) := by
  let K := coshWavePacket N F hF R hR hs
  let row := fun x => poincareSeedVector N (radialSeed (abelProfile F)
    (abelProfile_smooth F hF hc) x R hR (abelProfile_support F _ hs))
  apply positive_kernel_measurable_of_filtered (quotientMeasure N) D hD row
  intro B
  have hm (i : ι) : Measurable
      (fun x => ENNReal.ofReal (‖(K (B (b i))).val x‖^2)) :=
    ((Lp.stronglyMeasurable (K (B (b i))).val).norm.pow 2).measurable.ennreal_ofReal
  have hmeas : Measurable (fun x => ∑' i,ENNReal.ofReal (‖(K (B (b i))).val x‖^2)) :=
    Measurable.tsum hm
  have hsum := hmeas.ennreal_toReal.aestronglyMeasurable (μ:=quotientMeasure N)
  apply hsum.congr
  filter_upwards [coshWavePacket_filtered_pretrace N b B F hF hc hr R hR hs] with x hx
  change HasSum (fun i => ‖(K (B (b i))).val x‖^2) (‖B.adjoint (row x)‖^2) at hx
  rw [←ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hx.summable,hx.tsum_eq,
    ENNReal.toReal_ofReal (sq_nonneg _)]

/-- The literal LV geometric kernel is integrable as a real function,
not only measurable with a finite formal extended trace. -/
theorem actualLVFilter_kernel_integrable {ι κ : Type*} [Countable ι]
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a d : ℤ) (had : (p:ℤ)*a+(N:ℤ)*d=1) (k : ℕ)
    (b : HilbertBasis ι ℂ (AutomorphicSpace N))
    (c : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (he : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (c j:AutomorphicSpace N) ((e j:ℂ) • (c j:AutomorphicSpace N)))
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    Integrable (fun x => (inner ℂ
      (actualLVFilter N p hN hpN a d had k
        (poincareSeedVector N (radialSeed (abelProfile F) (abelProfile_smooth F hF hc)
          x R hR (abelProfile_support F _ hs))))
      (poincareSeedVector N (radialSeed (abelProfile F) (abelProfile_smooth F hF hc)
        x R hR (abelProfile_support F _ hs)))).re) (quotientMeasure N) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (cosh_positive_kernel_aestronglyMeasurable N b _
      (actualLVFilter_order N p hN hpN a d had k).1 F hF hc hr R hR hs)
    (Filter.Eventually.of_forall (fun x =>
      (ContinuousLinearMap.nonneg_iff_isPositive.mp
        (actualLVFilter_order N p hN hpN a d had k).1).re_inner_nonneg_left _))).mp
  exact (actualLVFilter_kernel_trace_finite_of_cusp_basis N p hN hpN hNp hpres a d had k
    b c e he hgraph F hF hc hr R hR hs).ne

/-- The scalar weighted trace converges as a real series. -/
theorem actualLVFilter_weighted_spectrum_summable {ι κ : Type*} [Countable ι]
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a d : ℤ) (had : (p:ℤ)*a+(N:ℤ)*d=1) (k : ℕ)
    (b : HilbertBasis ι ℂ (AutomorphicSpace N))
    (c : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (he : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (c j:AutomorphicSpace N) ((e j:ℂ) • (c j:AutomorphicSpace N)))
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    Summable (fun j => ‖smoothPacketMultiplier (coshTimeTest F) (e j)‖^2 *
        (inner ℂ (actualLVFilter N p hN hpN a d had k (c j:AutomorphicSpace N))
          (c j:AutomorphicSpace N)).re) := by
  have hfin := actualLVFilter_weighted_spectrum_finite N p hN hpN hNp hpres a d had k
    b c e he hgraph F hF hc hr R hR hs
  have h := ENNReal.summable_toReal hfin.ne
  have ho : Orthonormal ℂ (fun j => (c j:AutomorphicSpace N)) :=
    c.orthonormal.comp_linearIsometry (localCuspidalSpace N hN).subtypeₗᵢ
  apply h.congr
  intro j
  exact ENNReal.toReal_ofReal (mul_nonneg (sq_nonneg _)
    (actualLVFilter_cusp_weight_bounds N p hN hpN hNp hpres a d had k
      (c j:AutomorphicSpace N) (c j).property (ho.norm_eq_one j)).1)

/-- A real-valued geometric trace equals the convergent scalar spectral series. -/
theorem actualLVFilter_real_trace_eq_weighted_spectrum {ι κ : Type*} [Countable ι]
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a d : ℤ) (had : (p:ℤ)*a+(N:ℤ)*d=1) (k : ℕ)
    (b : HilbertBasis ι ℂ (AutomorphicSpace N))
    (c : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (he : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (c j:AutomorphicSpace N) ((e j:ℂ) • (c j:AutomorphicSpace N)))
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    (∫ x, (inner ℂ
      (actualLVFilter N p hN hpN a d had k
        (poincareSeedVector N (radialSeed (abelProfile F) (abelProfile_smooth F hF hc)
          x R hR (abelProfile_support F _ hs))))
      (poincareSeedVector N (radialSeed (abelProfile F) (abelProfile_smooth F hF hc)
        x R hR (abelProfile_support F _ hs)))).re ∂quotientMeasure N)=∑' j,‖smoothPacketMultiplier (coshTimeTest F) (e j)‖^2 *
        (inner ℂ (actualLVFilter N p hN hpN a d had k (c j:AutomorphicSpace N))
          (c j:AutomorphicSpace N)).re := by
  let row := fun x => poincareSeedVector N (radialSeed (abelProfile F)
    (abelProfile_smooth F hF hc) x R hR (abelProfile_support F _ hs))
  let q := fun x => (inner ℂ (actualLVFilter N p hN hpN a d had k (row x)) (row x)).re
  change (∫ x,q x ∂quotientMeasure N)=_
  have hm : AEStronglyMeasurable q (quotientMeasure N) :=
    cosh_positive_kernel_aestronglyMeasurable N b _
      (actualLVFilter_order N p hN hpN a d had k).1 F hF hc hr R hR hs
  have hp : 0≤ᵐ[quotientMeasure N] q := Filter.Eventually.of_forall (fun x =>
    (ContinuousLinearMap.nonneg_iff_isPositive.mp
      (actualLVFilter_order N p hN hpN a d had k).1).re_inner_nonneg_left (row x))
  rw [integral_eq_lintegral_of_nonneg_ae hp hm]
  change (∫⁻ x,ENNReal.ofReal ((inner ℂ
    (actualLVFilter N p hN hpN a d had k (row x)) (row x)).re) ∂quotientMeasure N).toReal=_
  rw [actualLVFilter_kernel_trace_eq_weighted_spectrum N p hN hpN hNp hpres a d had k
      b c e he hgraph F hF hc hr R hR hs,
    ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  have ho : Orthonormal ℂ (fun j => (c j:AutomorphicSpace N)) :=
    c.orthonormal.comp_linearIsometry (localCuspidalSpace N hN).subtypeₗᵢ
  apply tsum_congr
  intro j
  exact ENNReal.toReal_ofReal (mul_nonneg (sq_nonneg _)
    (actualLVFilter_cusp_weight_bounds N p hN hpN hNp hpres a d had k
      (c j:AutomorphicSpace N) (c j).property (ho.norm_eq_one j)).1)

#print axioms positive_kernel_measurable_of_filtered
#print axioms cosh_positive_kernel_aestronglyMeasurable
#print axioms actualLVFilter_kernel_integrable
#print axioms actualLVFilter_weighted_spectrum_summable
#print axioms actualLVFilter_real_trace_eq_weighted_spectrum

end QuantitativeMaass
