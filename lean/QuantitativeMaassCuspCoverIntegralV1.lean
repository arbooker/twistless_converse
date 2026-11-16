module

public import QuantitativeMaassCuspWindowIntegralV1
public import QuantitativeMaassCuspCoreGeometryV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels
open QuantitativeSpectralObservability
open scoped Topology MatrixGroups FourierTransform SchwartzMap ENNReal Pointwise

namespace QuantitativeMaass

/-- A nonnegative continuous integrand on the actual reduction core is bounded
by the sum of its integrals over the finitely many integral cusp charts. -/
theorem wideCompactCover_integral_bound (N : ℕ) (hN : 0<N) (H : ℝ)
    (f : ℍ → ℝ) (hf : Continuous f) (hn : ∀ z,0≤f z) (C : ℝ) (hC : 0≤C)
    (hb : ∀ A : SL(2,ℤ),(∫ z in wideBox H,f (A•z))≤C) :
    (∫ z in wideCompactCover N H,f z)≤
      (Nat.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N):ℝ)*C := by
  let : NeZero N := ⟨hN.ne'⟩
  let := Fintype.ofFinite (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  have hi : IntegrableOn f (wideCompactCover N H) volume := hf.continuousOn.integrableOn_compact (wideCompactCover_compact N hN H)
  have hle : (∫⁻ z in wideCompactCover N H,ENNReal.ofReal (f z))≤
      (Nat.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N):ℝ≥0∞)*ENNReal.ofReal C := by
    calc
      _ ≤ ∑' q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
          ∫⁻ z in (integralLabel q.out)⁻¹ • wideBox H,ENNReal.ofReal (f z) :=
        lintegral_iUnion_le _ _
      _ ≤ ∑' _q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N,ENNReal.ofReal C := by
        apply ENNReal.tsum_le_tsum
        intro q
        have ha : Isometry (fun z : ℍ => (integralLabel q.out)⁻¹•z) := by
          apply Isometry.of_dist_eq
          intro x y
          simp only [←map_inv,integralLabel_action,integral_action_dist]
        change (∫⁻ z in (fun w : ℍ => (integralLabel q.out)⁻¹•w) '' wideBox H,ENNReal.ofReal (f z))≤_
        rw [← (AsymptoticRationalGroup.measurePreserving ((integralLabel q.out)⁻¹)).setLIntegral_comp_emb
          ha.isClosedEmbedding.measurableEmbedding _ (wideBox H)]
        simp only [←map_inv,integralLabel_action]
        have ha : Continuous (fun z : ℍ => q.out⁻¹•z) :=
          (Isometry.of_dist_eq (fun x y => integral_action_dist q.out⁻¹ x y)).continuous
        have hiq : IntegrableOn (fun z => f (q.out⁻¹•z)) (wideBox H) volume :=
          (hf.comp ha).continuousOn.integrableOn_compact (wideBox_compact H)
        rw [← ofReal_integral_eq_lintegral_ofReal hiq (Eventually.of_forall (fun z => hn _))]
        exact ENNReal.ofReal_le_ofReal (hb q.out⁻¹)
      _ = _ := by simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,
          nsmul_eq_mul,Nat.card_eq_fintype_card]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hn)] at hle
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Nat.cast_nonneg _) hC)).mp
  simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast] using hle

/-- Continuity of the actual original-window nonidentity contribution. -/
theorem windowGeometricRemainder_continuous (N : ℕ) (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) :
    Continuous (windowGeometricRemainder N K hc R hR a b) := by
  obtain ⟨B,hB,hs⟩ := symmetricWindowTimeTest_uniform_support K hc
  let f := windowTimeSchwartz K hc R hR a b
  have hfe : Function.Even f := symmetricWindowTimeTest_even K he R a b
  have hfc : HasCompactSupport (f : ℝ → ℂ) := symmetricWindowTimeTest_compact K hc R a b hR
  have hgs := timeConvolution_support f f (B*R) (B*R) (hs R hR a b) (hs R hR a b)
  exact radialNonidentity_continuous N _
    (evenTime_abel_continuous (timeConvolution f f) ((timeConvolution f f).smooth ⊤)
      (timeConvolution_even f f hfe hfe) (timeConvolution_compact f f hfc hfc))
    (B*R+B*R) (by positivity)
    (abelProfile_support _ _ (evenCoshLift_support_of_time_support _ _ (by positivity) hgs))

/-- The fixed-radius nonidentity bound on the full actual compact reduction core. -/
theorem windowGeometricRemainder_fixedRadius_core_integral (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 1≤R) :
    ∃ C : ℝ,0<C ∧ ∀ (N : ℕ),0<N → ∀ ε t H : ℝ,
      0≤ε → ε≤1 → 1≤t → (1:ℝ)/4≤H →
      (∫ z in wideCompactCover N H,
        ‖windowGeometricRemainder N K hc R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) z‖)≤
        (Nat.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N):ℝ)*
          (C*Real.sqrt t*ε^2*(1+Real.sqrt H)) := by
  obtain ⟨C,hC,hbound⟩ := windowGeometricRemainder_fixedRadius_cusp_integral K he hc R hR
  refine ⟨C,hC,?_⟩
  intro N hN ε t H hε hε1 ht hH
  exact wideCompactCover_integral_bound N hN H _
    (windowGeometricRemainder_continuous N K he hc R _ (t-ε) (t+ε)).norm
    (fun z => norm_nonneg _) _ (by positivity)
    (fun A => hbound N A ε t H hε hε1 ht hH)

#print axioms wideCompactCover_integral_bound
#print axioms windowGeometricRemainder_continuous
#print axioms windowGeometricRemainder_fixedRadius_core_integral

end QuantitativeMaass
