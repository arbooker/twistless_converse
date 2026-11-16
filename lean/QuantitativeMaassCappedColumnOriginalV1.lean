module

public import QuantitativeMaassCylinderCappedColumnsV1
public import QuantitativeMaassEulerTimePacketV1
public import QuantitativeMaassPacketDiagonalV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- The finite-band column has the exact original Euler multiplier at
every point. Finite propagation removes the inverse-weight truncation. -/
theorem cylinderCappedAbelColumn_original {N Q : ℕ} {hQ : 0<Q}
    (hN : 0<N) (A : FinitenessCertificate.Certificate N Q hQ)
    (P : FinitenessGlobalHeight.Parameters A) (r : ℝ) (σ : ℕ) {b : ℕ → ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) (x : ℍ) :
    inner ℂ (LogBands.conjugatedColumn (quotientMeasure 0)
      (fun z => Real.log (cappedHeightWeight P.ε (P.s+3) z))
      (cappedHeightWeight_log_measurable P.ε (P.s+3))
      (cylinderAbelColumn F hF.contDiffOn R hR hs) ⌈((P.s+3:ℕ):ℝ)*R+1⌉₊ x)
      (principalEulerCylinderLp hN A P r σ hb) =
      cosinePacket (coshTimeTest F) r *
        ((cappedHeightWeight P.ε (P.s+3) x:ℂ)*principalEulerPhysical b r σ x) := by
  let l := fun z : ℍ => Real.log (cappedHeightWeight P.ε (P.s+3) z)
  let hl := cappedHeightWeight_log_measurable P.ε (P.s+3)
  let J : ℕ := ⌈((P.s+3:ℕ):ℝ)*R+1⌉₊
  let D := radialKernelData 0 (abelProfile F) (abelProfile_smooth F hF hc)
    R hR (abelProfile_support F _ hs)
  let v := principalEulerCylinderLp hN A P r σ hb
  have hk : ∀ n m : ℤ,(J:ℤ) < |n-m| →
      ∀ z∈LogBands.region l n,∀ w∈LogBands.region l m,D.kernel z w=0 := by
    intro n m hnm z hz w hw
    apply cylinder_radial_kernel_band_zero (abelProfile F) R hR
      (abelProfile_support F _ hs) P.epsilon_pos (P.s+3) n m z w hz hw
    have hh : (J:ℝ) < |(n:ℝ)-(m:ℝ)| := by exact_mod_cast hnm
    exact (Nat.le_ceil _).trans hh.le
  have he : (fun y => (Real.exp (-l y):ℂ)*v y)=ᵐ[quotientMeasure 0]
      (fun y => principalEulerPhysical b r σ y) := by
    filter_upwards [principalEulerCylinderLp_coeFn hN A P r σ hb] with y hy
    change v y=AsymptoticWeightedBranches.weighted P.ε (P.s+3) 0
      (principalEulerPhysical b r σ) y at hy
    rw [hy,weighted_zero_eq_capped]
    exact cappedHeightWeight_inverse_cancel P.epsilon_pos (P.s+3) y _
  rw [LogBands.conjugatedColumn_inner,cylinderAbelColumn_inner F hF.contDiffOn hr]
  change (Real.exp (l x):ℂ)*D.output
    (LogBands.rowInverseSum (quotientMeasure 0) l hl J ⌊l x⌋ v) x=_
  have hrow : LogBands.rowInverseSum (quotientMeasure 0) l hl J ⌊l x⌋ v =
      ∑ m∈Finset.Icc (⌊l x⌋-(J:ℤ)) (⌊l x⌋+(J:ℤ)),
        LogBands.inverse (quotientMeasure 0) l hl m v := by
    simp only [LogBands.rowInverseSum,sum_apply]
  rw [hrow,LogBands.kernel_output_inverse_sum (quotientMeasure 0) l hl D J hk
    ⌊l x⌋ v x (LogBands.mem_floor_region l x),D.output_congr_ae he]
  rw [(continuous_radial_output_unfold 0 (abelProfile F) (abelProfile_smooth F hF hc)
    R hR (abelProfile_support F _ hs) (fun y => principalEulerPhysical b r σ y)
    (principalEulerPhysical_continuous_upper hb.polynomialGrowth r σ)
    (principalEulerPhysical_cylinder_invariant b r σ) x).2.2,
    principalEuler_abel_multiplier hb.polynomialGrowth r σ F hF hc hr R hR hs x]
  dsimp only [l]
  rw [Real.exp_log (cappedHeightWeight_pos P.epsilon_pos (P.s+3) x)]
  ring

/-- Strong convergence of literal columns extends the pointwise identity
to the original smooth time test, before averaging over a horizontal curve. -/
theorem cylinderCappedTimeColumn_original {N Q : ℕ} {hQ : 0<Q}
    (hN : 0<N) (A : FinitenessCertificate.Certificate N Q hQ)
    (P : FinitenessGlobalHeight.Parameters A) (r : ℝ) (σ : ℕ) {b : ℕ → ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f)
    (hc : HasCompactSupport f) (hr : ∀ s,star (f s)=f s)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) (x : ℍ) :
    inner ℂ (cylinderCappedTimeColumn f hf he hc R hR
      (evenCoshLift_support_of_time_support f R hR hs) P.ε (P.s+3) x)
      (principalEulerCylinderLp hN A P r σ hb) =
      cosinePacket f r *
        ((cappedHeightWeight P.ε (P.s+3) x:ℂ)*principalEulerPhysical b r σ x) := by
  let a : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have ha (n : ℕ) : 0<a n := by dsimp [a]; positivity
  have ha0 : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let F := evenCoshLift f
  have hF : ContDiffOn ℝ ∞ F (Ici 1) := evenCoshLift_smoothOn f hf he hc
  have hsF : Function.support F⊆Iic (Real.cosh R) :=
    evenCoshLift_support_of_time_support f R hR hs
  have hz : ∀ q,Real.cosh R<q → F q=0 := evenCoshLift_zero_above f R hR hs
  let C (n : ℕ) := cylinderAbelColumn (radialShiftApprox F (a n))
    (radialShiftApprox_smooth F hF _ (ha n)).contDiffOn R hR
    (radialShiftApprox_upper_support F _ hz _ (ha n)) x
  let S := (LogBands.rowInverseSum (quotientMeasure 0)
    (fun z => Real.log (cappedHeightWeight P.ε (P.s+3) z))
    (cappedHeightWeight_log_measurable P.ε (P.s+3))
    ⌈((P.s+3:ℕ):ℝ)*R+1⌉₊ ⌊Real.log (cappedHeightWeight P.ε (P.s+3) x)⌋).adjoint
  let w : ℂ := (Real.exp (Real.log (cappedHeightWeight P.ε (P.s+3) x)):ℂ)
  have hC : Tendsto C atTop (𝓝 (cylinderAbelColumn F hF R hR hsF x)) :=
    cylinderAbelColumn_shift_tendsto atTop F hF R hR hsF a ha ha0 x
  have hleft := ((S.continuous.tendsto _).comp (hC.const_smul w)).inner (𝕜:=ℂ)
    (tendsto_const_nhds (x:=principalEulerCylinderLp hN A P r σ hb))
  have hright := (radialShiftTime_cosinePacket_tendsto atTop f hf he hc R hR hs a ha ha0 r).mul_const
    ((cappedHeightWeight P.ε (P.s+3) x:ℂ)*principalEulerPhysical b r σ x)
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  filter_upwards with n
  exact (cylinderCappedAbelColumn_original hN A P r σ hb (radialShiftApprox F (a n))
    (radialShiftApprox_smooth F hF _ (ha n)) (radialShiftApprox_compact F _ hz _ (ha n))
    (radialShiftApprox_real F (evenCoshLift_real f hr) (a n)) R hR
    (radialShiftApprox_upper_support F _ hz _ (ha n)) x).symm

#print axioms cylinderCappedAbelColumn_original
#print axioms cylinderCappedTimeColumn_original

end QuantitativeMaass
