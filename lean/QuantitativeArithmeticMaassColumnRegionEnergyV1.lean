module

public import QuantitativeArithmeticMaassSourceColumnEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff SchwartzMap ENNReal

namespace QuantitativeMaass

/-- Restriction to a small region preserves its actual volume in the
identity term; only the nonscalar remainder is bounded on the containing
ball. This is the estimate needed for shrinking cutoff collars. -/
theorem radialIntegralKernel_region_bound (N : ℕ)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0 < M.det)
    (g : ℝ → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hs : Function.support g ⊆ Iic (Real.cosh R)) (o : ℍ) (L D E : ℝ)
    (Ω : Set ℍ) (hΩ : Ω ⊆ Metric.closedBall o L)
    (hD : 0 ≤ D) (hd : ‖g 1‖ ≤ D)
    (hi : IntegrableOn (radialIntegralRemainder N M hM g) (Metric.closedBall o L))
    (hb : (∫ z in Metric.closedBall o L, ‖radialIntegralRemainder N M hM g z‖) ≤ E) :
    IntegrableOn (fun z => radialPoincareKernel N g z (positiveIntegralGL M hM • z)) Ω ∧
    (∫ z in Ω, ‖radialPoincareKernel N g z (positiveIntegralGL M hM • z)‖) ≤
      volume.real Ω*D+E := by
  classical
  let c : ℂ := if integralIdentityCoset N M then g 1 else 0
  have hc : ‖c‖ ≤ D := by
    dsimp only [c]
    split_ifs
    · exact hd
    · simpa using hD
  have hic : IntegrableOn (fun _z : ℍ => c) Ω :=
    (continuous_const.continuousOn.integrableOn_compact (isCompact_closedBall o L)).mono_set hΩ
  have hiΩ := hi.mono_set hΩ
  have hrem : (∫ z in Ω, ‖radialIntegralRemainder N M hM g z‖) ≤ E :=
    (setIntegral_mono_set hi.norm (Filter.Eventually.of_forall (fun z => norm_nonneg _))
      (Filter.Eventually.of_forall hΩ)).trans hb
  have hsplit (z : ℍ) : radialPoincareKernel N g z (positiveIntegralGL M hM • z) =
      c + radialIntegralRemainder N M hM g z :=
    radialIntegralKernel_identity_split N M hM g R hR hs z
  have hik : IntegrableOn (fun z => radialPoincareKernel N g z
      (positiveIntegralGL M hM • z)) Ω :=
    (hic.add hiΩ).congr (Filter.Eventually.of_forall (fun z => (hsplit z).symm))
  refine ⟨hik,?_⟩
  calc
    _ ≤ ∫ z in Ω, ‖c‖ + ‖radialIntegralRemainder N M hM g z‖ := by
      apply integral_mono_ae hik.norm (hic.norm.add hiΩ.norm)
      exact Filter.Eventually.of_forall (fun z => by
        dsimp only [Pi.add_apply]
        rw [hsplit]
        exact norm_add_le _ _)
    _ = volume.real Ω*‖c‖ + ∫ z in Ω, ‖radialIntegralRemainder N M hM g z‖ := by
      rw [integral_add hic.norm hiΩ.norm]
      simp [measureReal_def]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hc ENNReal.toReal_nonneg) hrem

/-- Column energy in a collar has a main term proportional to the collar's
volume, with a uniform geometric remainder from its containing ball. -/
theorem cylinderTimeColumn_region_energy (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ → ℂ)) (he : Function.Even f)
    (hr : ∀ s, star (f s) = f s) (R : ℝ) (hR : 0 ≤ R)
    (hs : Function.support f ⊆ Icc (-R) R) (o : ℍ) (L C D : ℝ)
    (Ω : Set ℍ) (hΩ : Ω ⊆ Metric.closedBall o L) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hd : ‖abelProfile (evenCoshLift (timeConvolution f f)) 1‖ ≤ D)
    (hb : ∀ d : ℝ, 0 < d →
      ‖abelProfile (evenCoshLift (timeConvolution f f)) (Real.cosh d)‖ ≤
        C/Real.sqrt (Real.sinh d)) :
    (∫ z in Ω, ‖cylinderTimeColumn f hc he R hR hs z‖^2) ≤
      volume.real Ω*D+
      (QuantitativeArithmeticMaassOverlap.energyMultiplicity o 0 (2*R+2*L) : ℝ)*C*
        (Real.pi*(volume.real (Metric.closedBall o L)+
          hyperbolicSublevelConstant o L (2*R+2*L+2*Real.log 2))) := by
  let g := abelProfile (evenCoshLift (timeConvolution f f))
  have hg : ContinuousOn g (Ici 1) := evenTime_abel_continuous _
    ((timeConvolution f f).smooth ⊤) (timeConvolution_even f f he he)
    (timeConvolution_compact f f hc hc)
  have hcs : Function.support (timeConvolution f f : ℝ → ℂ) ⊆ Icc (-(2*R)) (2*R) := by
    simpa only [two_mul] using timeConvolution_support f f R R hs hs
  have hgs : Function.support g ⊆ Iic (Real.cosh (2*R)) :=
    abelProfile_support _ _ (evenCoshLift_support_of_time_support _ _ (by positivity) hcs)
  have hId : 0 < (1 : Matrix (Fin 2) (Fin 2) ℤ).det := by simp
  have hact (z : ℍ) : positiveIntegralGL 1 hId • z = z := by
    apply UpperHalfPlane.ext
    rw [positiveIntegralGL_fractional]
    simp
  have hentry : ∀ i j : Fin 2, |((1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℝ)| ≤ 1 := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num
  obtain ⟨hi,hrem⟩ := radialIntegralRemainder_all_integral_bound 0 1 hId 1 (by norm_num)
    hentry o L (2*R) (by positivity) g hg hgs C hC hb
  simp only [hact, dist_self, add_zero, mul_one] at hrem
  obtain ⟨hki,hbound⟩ := radialIntegralKernel_region_bound 0 1 hId g
    (2*R) (by positivity) hgs o L D _ Ω hΩ hD hd hi hrem
  simp only [hact] at hki hbound
  calc
    _ = ∫ z in Ω, (radialPoincareKernel 0 g z z).re := by
      apply integral_congr_ae
      filter_upwards with z
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), cylinderTimeSquare_kernel_cross f hc he hr R hR hs]
      rfl
    _ ≤ ∫ z in Ω, ‖radialPoincareKernel 0 g z z‖ :=
      integral_mono_ae hki.re hki.norm
        (Filter.Eventually.of_forall (fun z => Complex.re_le_norm _))
    _ ≤ _ := hbound

#print axioms radialIntegralKernel_region_bound
#print axioms cylinderTimeColumn_region_energy

end QuantitativeMaass
