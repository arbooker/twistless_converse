module

public import QuantitativeMaassEvenPacketPretraceV1
public import QuantitativeArithmeticMaassOverlapEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson QuantitativeArithmeticMaassOverlap
open scoped Topology ContDiff ENNReal

namespace QuantitativeMaass

/-- Actual quotient row energies converge. This gives a direct passage of
explicit geometric inequalities, without assuming trace continuity. -/
theorem radialShiftAbelKernel_row_energy_tendsto {ι : Type*} (l : Filter ι) [l.IsCountablyGenerated]
    (N : ℕ) [NeZero N] (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R))
    (a : ι → ℝ) (ha : ∀ i,0<a i) (ha0 : Tendsto a l (𝓝 0)) (x : ℍ) :
    Tendsto (fun i => ∫ y,‖radialPoincareKernel N (abelProfile (radialShiftApprox F (a i))) x y‖^2
      ∂quotientMeasure N) l
      (𝓝 (∫ y,‖radialPoincareKernel N (abelProfile F) x y‖^2 ∂quotientMeasure N)) := by
  have hz : ∀ q,Real.cosh R<q → F q=0 := fun q hq => by
    by_contra hn
    exact (not_le_of_gt hq) (hs hn)
  obtain ⟨D,_,hbound⟩ := radialShiftAbelKernel_local_bound N F hF R hR hs x 0
  have hm (i : ι) : AEStronglyMeasurable (fun y =>
      ‖radialPoincareKernel N (abelProfile (radialShiftApprox F (a i))) x y‖^2) (quotientMeasure N) := by
    have h := radialPoincareKernel_joint_measurable N _ (abelProfile_smooth _
      (radialShiftApprox_smooth F hF _ (ha i)) (radialShiftApprox_compact F _ hz _ (ha i))).continuous
    exact (Measurable.of_uncurry_left
      (f:=radialPoincareKernel N (abelProfile (radialShiftApprox F (a i)))) h).norm.pow_const 2
      |>.aestronglyMeasurable
  have hb : ∀ᶠ i in l,∀ᵐ y ∂quotientMeasure N,
      ‖‖radialPoincareKernel N (abelProfile (radialShiftApprox F (a i))) x y‖^2‖≤D^2 := by
    filter_upwards [(tendsto_order.1 ha0).2 1 (by norm_num)] with i hi
    filter_upwards with y
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbound _ (ha i) hi.le x (by simp) y) 2
  have hl : ∀ᵐ y ∂quotientMeasure N,Tendsto (fun i =>
      ‖radialPoincareKernel N (abelProfile (radialShiftApprox F (a i))) x y‖^2) l
      (𝓝 (‖radialPoincareKernel N (abelProfile F) x y‖^2)) := by
    filter_upwards with y
    exact (radialShiftAbelKernel_tendsto l N F hF R hR hs a ha ha0 x y).norm.pow 2
  exact tendsto_integral_filter_of_dominated_convergence (fun _ => D^2)
    (Eventually.of_forall hm) hb (integrable_const _) hl

/-- The explicit lattice multiplicity passes to the original one-sided
radial test. The entire radial energy is retained in the bound. -/
theorem oneSidedAbelKernel_row_energy_explicit (N : ℕ) [NeZero N]
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R))
    (o : ℍ) (L : ℝ) (x : ℍ) (hx : dist x o≤L) :
    (∫ y,‖radialPoincareKernel N (abelProfile F) x y‖^2 ∂quotientMeasure N)≤
      (energyMultiplicity o L R:ℝ)*((2*Real.pi)*∫ q in Ioi (1:ℝ),‖abelProfile F q‖^2) := by
  let a : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have ha (n : ℕ) : 0<a n := by dsimp [a]; positivity
  have ha0 : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hz : ∀ q,Real.cosh R<q → F q=0 := fun q hq => by
    by_contra hn
    exact (not_le_of_gt hq) (hs hn)
  let g (n : ℕ) := abelProfile (radialShiftApprox F (a n))
  have hg (n : ℕ) : ContDiff ℝ ∞ (g n) := abelProfile_smooth _
    (radialShiftApprox_smooth F hF _ (ha n)) (radialShiftApprox_compact F _ hz _ (ha n))
  have hgs (n : ℕ) : Function.support (g n)⊆Iic (Real.cosh R) :=
    abelProfile_support _ _ (radialShiftApprox_upper_support F _ hz _ (ha n))
  have hb (n : ℕ) : (∫ y,‖radialPoincareKernel N (g n) x y‖^2 ∂quotientMeasure N)≤
      (energyMultiplicity o L R:ℝ)*((2*Real.pi)*∫ q in Ioi (1:ℝ),‖g n q‖^2) := by
    have h := radialKernel_compact_energy_explicit N o L R hR (g n) (hg n) (hgs n) x hx
    have hnonneg : 0≤(2*Real.pi)*∫ q in Ioi (1:ℝ),‖g n q‖^2 :=
      mul_nonneg (by positivity) (integral_nonneg (fun _ => sq_nonneg _))
    have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) h
    rw [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofReal (sq_nonneg _),
      ENNReal.toReal_ofReal hnonneg,radialKernel_row_energy] at ht
    exact ht
  exact le_of_tendsto_of_tendsto'
    (radialShiftAbelKernel_row_energy_tendsto atTop N F hF R hR hs a ha ha0 x)
    ((radialShiftAbelProfile_energy_tendsto atTop F hF _ (Real.one_le_cosh R) hs a ha ha0).const_mul
      (2*Real.pi) |>.const_mul (energyMultiplicity o L R:ℝ)) hb

theorem oneSidedAbelKernel_local_energy_explicit (N : ℕ) [NeZero N]
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) (o : ℍ) (L : ℝ) :
    (∫⁻ x in Metric.closedBall o L,∫⁻ y,
      ENNReal.ofReal (‖radialPoincareKernel N (abelProfile F) x y‖^2)
      ∂quotientMeasure N ∂quotientMeasure N)≤
      ((energyMultiplicity o L R:ℝ≥0∞)*
        ENNReal.ofReal ((2*Real.pi)*∫ q in Ioi (1:ℝ),‖abelProfile F q‖^2))*
          quotientMeasure N (Metric.closedBall o L) := by
  calc
    _ ≤ ∫⁻ _x in Metric.closedBall o L,
        (energyMultiplicity o L R:ℝ≥0∞)*
          ENNReal.ofReal ((2*Real.pi)*∫ q in Ioi (1:ℝ),‖abelProfile F q‖^2)
          ∂quotientMeasure N := by
      apply setLIntegral_mono' Metric.isClosed_closedBall.measurableSet
      intro x hx
      rw [← oneSidedAbelColumn_lintegral N F hF R hR hs x]
      have h := ENNReal.ofReal_le_ofReal (oneSidedAbelKernel_row_energy_explicit N F hF R hR hs o L x hx)
      simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast] using h
    _ = _ := by rw [lintegral_const,Measure.restrict_apply_univ]

/-- Explicit local spectral energy bound for the original time packet. -/
theorem evenWavePacket_local_energy_explicit {ι : Type*} [Countable ι]
    (N : ℕ) [NeZero N] (basis : HilbertBasis ι ℂ (AutomorphicSpace N)) (o : ℍ) (L : ℝ)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f) (hc : HasCompactSupport f)
    (hr : ∀ t,star (f t)=f t) (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    (∑' i,∫⁻ x in Metric.closedBall o L,ENNReal.ofReal
      (‖(Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f hf hc) (basis i)).val x‖^2)
      ∂quotientMeasure N)≤
      ((energyMultiplicity o L R:ℝ≥0∞)*
        ENNReal.ofReal ((2*Real.pi)*∫ q in Ioi (1:ℝ),‖abelProfile (evenCoshLift f) q‖^2))*
          quotientMeasure N (Metric.closedBall o L) := by
  rw [evenWavePacket_restricted_energy_trace N basis _ f hf he hc hr R hR hs]
  apply oneSidedAbelKernel_local_energy_explicit N _ (evenCoshLift_smoothOn f hf he hc) R hR
  intro q hq
  by_contra hn
  exact hq (evenCoshLift_zero_above f R hR hs q (lt_of_not_ge hn))

/-- A usable exponential upper bound for the explicit lattice multiplicity. -/
theorem energyMultiplicity_exp_bound (o : ℍ) (L R : ℝ) (hL : 0≤L) (hR : 0≤R) :
    (energyMultiplicity o L R:ℝ)≤625*Real.exp (4*(R+L+1+dist o I)) := by
  have hS : 0≤R+L+1+dist o I := by positivity
  have he : 1≤Real.exp (R+L+1+dist o I) := Real.one_le_exp_iff.mpr hS
  have hceil := (Nat.ceil_lt_add_one (Real.exp_pos (R+L+1+dist o I)).le).le
  have hb : (2*⌈Real.exp (R+L+1+dist o I)⌉₊+1:ℝ)≤5*Real.exp (R+L+1+dist o I) := by linarith
  unfold energyMultiplicity
  push_cast
  apply (pow_le_pow_left₀ (by positivity) hb 4).trans_eq
  rw [mul_pow,← Real.exp_nat_mul]
  norm_num

#print axioms radialShiftAbelKernel_row_energy_tendsto
#print axioms oneSidedAbelKernel_row_energy_explicit
#print axioms oneSidedAbelKernel_local_energy_explicit
#print axioms evenWavePacket_local_energy_explicit
#print axioms energyMultiplicity_exp_bound

end QuantitativeMaass
