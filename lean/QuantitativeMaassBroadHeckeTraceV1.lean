module

public import QuantitativeMaassBroadHeckeKernelV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology SchwartzMap

namespace QuantitativeMaass

/-- Uniform local-volume trace estimate for the actual broad packet
with one wave and an arbitrary Hecke power. -/
theorem broadAbelColumn_mixed_volume_trace_bound (o : ℍ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N p : ℕ) [NeZero N] [Fact p.Prime]
      (hN : 0 < N) (hpN : ¬p∣N) (_hNp : (N:ZMod p) ≠ 0)
      (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
      (S L t τ : ℝ) (hL : 1 ≤ L), 0 ≤ S → 1 ≤ t →
      ∀ (K : Set ℍ), IsCompact K → K ⊆ Metric.closedBall o S → ∀ n : ℕ,
      |(∫ z in K, (inner ℂ (Wave.shiftedQuotientWave N τ
          (((HeckeL2.operator N p hN hpN a b hab)^n)
            (broadAbelColumn N L (lt_of_lt_of_le zero_lt_one hL) t z)))
          (broadAbelColumn N L (lt_of_lt_of_le zero_lt_one hL) t z)).re) -
        volume.real K*((Real.sqrt (p:ℝ))⁻¹^n*(treeWalkCount (p+1) n 0:ℝ)*
          (broadTranslatedProfile L (lt_of_lt_of_le zero_lt_one hL) t τ 1).re)| ≤
        (heckeWordErrorGrowth p)^n*C*(1+|τ|)*Real.sqrt t*L^6*Real.exp (30*S+10*|τ|) := by
  obtain ⟨C,hC,hbound⟩ := upperBroadRemainder_growing_bound o
  refine ⟨C*3^40, by positivity, ?_⟩
  intro N p _ _ hN hpN hNp a b hab S L t τ hL hS ht K hK hKS n
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  simp_rw [broadAbelColumn_wave_hecke_power N p hN hpN hNp a b hab]
  let F := upperBroadRemainder N p L hLp t τ n HeckeUpper.root
  let c := (Real.sqrt (p:ℝ))⁻¹^n*(treeWalkCount (p+1) n 0:ℝ)*
    (broadTranslatedProfile L hLp t τ 1).re
  have hr : 0 < HeckeUpper.root.matrix.det := by
    norm_num [HeckeUpper.det_matrix, HeckeUpper.root_det]
  have hh := hbound N p S L t τ hL hS ht n HeckeUpper.root hr
  have hfv : IntegrableOn F (Metric.closedBall o S) := hh.1
  have hfi : IntegrableOn F K := hfv.mono_set hKS
  have hfri : IntegrableOn (fun z => (F z).re) K := hfi.re
  have heq : (fun z => (upperBroadKernel N p L hLp t τ n HeckeUpper.root z).re) =
      fun z => c+(F z).re := by
    funext z
    rw [upperBroadKernel_split N p L hL t τ n _ hr z, HeckeUpper.rawWalks_root_eq_tree]
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, ← Complex.ofReal_pow,
      Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im,
      zero_mul, mul_zero, zero_add, sub_zero]
    rfl
  have hci : IntegrableOn (fun _ : ℍ => c) K :=
    continuous_const.continuousOn.integrableOn_compact hK
  rw [heq]
  change |(∫ z in K, c+(F z).re)-volume.real K*c| ≤ _
  rw [integral_add hci hfri, integral_const, measureReal_restrict_apply_univ, smul_eq_mul,
    add_sub_cancel_left]
  calc
    _ ≤ ∫ z in K, ‖(F z).re‖ := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (μ := volume.restrict K) (fun z => (F z).re)
    _ ≤ ∫ z in K, ‖F z‖ := integral_mono hfri.norm hfi.norm
      (fun z => by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (F z))
    _ ≤ ∫ z in Metric.closedBall o S, ‖F z‖ := integral_mono_measure
      (Measure.restrict_mono_set volume hKS)
      (Eventually.of_forall (fun z => norm_nonneg (F z))) hfv.norm
    _ ≤ _ := by
      have hrh : integralMatrixHeight HeckeUpper.root.matrix = 3 := by
        norm_num [integralMatrixHeight, HeckeUpper.matrix, HeckeUpper.root]
      have hb := hh.2
      rw [hrh] at hb
      convert hb using 1
      ring

#print axioms broadAbelColumn_mixed_volume_trace_bound

end QuantitativeMaass
