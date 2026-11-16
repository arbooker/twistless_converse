module

public import QuantitativeMaassReflectionOperatorV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace SchwartzMap

namespace QuantitativeMaass

/-- Reflection covariance of the literal Poincare kernel, by a permutation
of the actual projective congruence group. No convergence assumption is needed. -/
theorem radialPoincareKernel_reflection (N : ℕ) (g : ℝ → ℂ) (x y : ℍ) :
    radialPoincareKernel N g (J•x) (J•y)=radialPoincareKernel N g x y := by
  simp only [radialPoincareKernel,poincareSum,radialFunction_upper]
  have he := (reflectedCongruenceEquiv N).tsum_eq
    (fun γ : gamma N => g (Real.cosh (dist (γ•(J•y)) (J•x))))
  have hx (γ : gamma N) :
      g (Real.cosh (dist ((reflectedCongruenceEquiv N γ)•(J•y)) (J•x)))=
        g (Real.cosh (dist (γ•y) x)) := by
    change g (Real.cosh (dist ((reflectedCongruence N γ)•(J•y)) (J•x)))=_
    rw [reflectedCongruence_action,reflection_involutive,reflection_dist]
  simp_rw [hx] at he
  exact he.symm

theorem radialPoincareKernel_reflection_swap (N : ℕ) (g : ℝ → ℂ) (x y : ℍ) :
    radialPoincareKernel N g x (J•y)=radialPoincareKernel N g (J•x) y := by
  simpa only [reflection_involutive] using radialPoincareKernel_reflection N g (J•x) y

/-- The completed Abel column retains literal invariance in its centre. -/
theorem oneSidedAbelColumn_invariant (N : ℕ) [NeZero N]
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R))
    (γ : gamma N) (x : ℍ) :
    oneSidedAbelColumn N F hF R hR hs (γ•x)=oneSidedAbelColumn N F hF R hR hs x := by
  unfold oneSidedAbelColumn
  apply congrArg (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N))
  apply Subtype.ext
  funext y
  exact radialPoincareKernel_center_invariant N (abelProfile F) x y γ

/-- The actual Hilbert reflection sends each literal Abel column at x to
its column at Jx. The proof is on representatives before completion. -/
theorem reflectionIsometry_abelColumn (N : ℕ) [NeZero N]
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) (x : ℍ) :
    reflectionIsometry N (oneSidedAbelColumn N F hF R hR hs x)=
      oneSidedAbelColumn N F hF R hR hs (J•x) := by
  unfold oneSidedAbelColumn
  rw [reflectionIsometry_apply]
  apply congrArg (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N))
  apply Subtype.ext
  funext y
  exact radialPoincareKernel_reflection_swap N (abelProfile F) x y

/-- Reflection of an actual invariant representative of an arbitrary Hilbert
vector. This does not compose an arbitrary AE representative with J. -/
theorem reflectionIsometry_coeFn_of_representative (N : ℕ) (v : AutomorphicSpace N)
    (f : ℍ → ℂ) (hf : Measurable f) (hinv : ∀ γ : gamma N,∀ z,f (γ•z)=f z)
    (hrep : v.val=ᵐ[quotientMeasure N]f) :
    (reflectionIsometry N v).val=ᵐ[quotientMeasure N](fun z => f (J•z)) := by
  have hm : MemLp f 2 (quotientMeasure N) := (Lp.memLp v.val).ae_eq hrep
  let u : AutomorphicL2.representatives (gamma N) (quotientMeasure N) := ⟨f,hf,hinv,hm⟩
  have he : AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) u=v := by
    apply Subtype.ext
    apply Lp.ext
    exact hm.coeFn_toLp.trans hrep.symm
  rw [← he,reflectionIsometry_apply]
  exact (reflectionRepresentative N u).property.2.2.coeFn_toLp

/-- A genuine continuous covariant column representation makes its operator
commute with the actual Hilbert reflection. -/
theorem reflection_commute_of_columns (N : ℕ)
    (A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (c : ℍ → AutomorphicSpace N) (hc : Continuous c)
    (hinv : ∀ γ : gamma N,∀ z,c (γ•z)=c z)
    (hj : ∀ z,reflectionIsometry N (c z)=c (J•z))
    (hrep : ∀ v,(A v).val=ᵐ[quotientMeasure N](fun z => inner ℂ (c z) v)) :
    Commute (reflectionIsometry N).toContinuousLinearMap A := by
  apply ContinuousLinearMap.ext
  intro v
  apply Subtype.ext
  apply Lp.ext
  have hu := reflectionIsometry_coeFn_of_representative N (A v)
    (fun z => inner ℂ (c z) v) (hc.inner continuous_const).measurable
    (fun γ z => by rw [hinv]) (hrep v)
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (reflectionIsometry_selfAdjoint N)
  filter_upwards [hu,hrep (reflectionIsometry N v)] with z hz hv
  change (reflectionIsometry N (A v)).val z=(A (reflectionIsometry N v)).val z
  rw [hz,hv,← hj]
  exact hs (c z) v

/-- Every original compact real even wave packet commutes with the proved
reflection involution, using its actual physical Abel kernel. -/
theorem evenWavePacket_reflection_commute (N : ℕ) [NeZero N]
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    Commute (reflectionIsometry N).toContinuousLinearMap
      (Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f (f.smooth ⊤) hc)) := by
  let F := evenCoshLift f
  have hF : ContDiffOn ℝ ∞ F (Ici 1) := evenCoshLift_smoothOn f (f.smooth ⊤) he hc
  have hsF : Function.support F⊆Iic (Real.cosh R) := evenCoshLift_support_of_time_support f R hR hs
  apply reflection_commute_of_columns N _ (oneSidedAbelColumn N F hF R hR hsF)
    (oneSidedAbelColumn_continuous N F hF R hR hsF)
    (oneSidedAbelColumn_invariant N F hF R hR hsF)
    (reflectionIsometry_abelColumn N F hF R hR hsF)
  intro v
  simp_rw [oneSidedAbelColumn_inner N F hF (evenCoshLift_real f hr) R hR hsF]
  exact evenWavePacket_kernel_coeFn N f (f.smooth ⊤) he hc hr R hR hs v

#print axioms radialPoincareKernel_reflection
#print axioms radialPoincareKernel_reflection_swap
#print axioms oneSidedAbelColumn_invariant
#print axioms reflectionIsometry_abelColumn
#print axioms reflectionIsometry_coeFn_of_representative
#print axioms reflection_commute_of_columns
#print axioms evenWavePacket_reflection_commute

end QuantitativeMaass
