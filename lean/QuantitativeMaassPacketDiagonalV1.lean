module

public import QuantitativeMaassAbelColumnContinuityV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace SchwartzMap FourierTransform

namespace QuantitativeMaass

/-- A continuous-column kernel square identity on the measure support.
The proof upgrades AE output identities before evaluating on the diagonal. -/
theorem selfAdjoint_kernel_square_diagonal (N : ℕ)
    (A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) (hA : IsSelfAdjoint A)
    (c d : ℍ → AutomorphicSpace N) (hc : Continuous c) (hd : Continuous d)
    (K : ℍ → ℍ → ℂ) (hK : ∀ x,Continuous (K x))
    (hrep : ∀ v,(A v).val=ᵐ[quotientMeasure N](fun x => inner ℂ (c x) v))
    (hsqrep : ∀ v,(A (A v)).val=ᵐ[quotientMeasure N](fun x => inner ℂ (d x) v))
    (hdrep : ∀ x,(d x).val=ᵐ[quotientMeasure N]K x)
    (x : ℍ) (hx : x∈(quotientMeasure N).support) :
    ((‖c x‖^2 : ℝ):ℂ)=K x x := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  have hAd : A (c x)=d x := by
    apply ext_inner_right ℂ
    intro v
    have hsym : inner ℂ (A (c x)) v=inner ℂ (c x) (A v) := hs (c x) v
    apply hsym.trans
    exact continuous_eq_on_measure_support (quotientMeasure N) _ _
      (hc.inner continuous_const) (hd.inner continuous_const)
      ((hrep (A v)).symm.trans (hsqrep v)) hx
  have he : (fun y => inner ℂ (c y) (c x))=ᵐ[quotientMeasure N]K x := by
    have hh := (hrep (c x)).symm
    rw [hAd] at hh
    exact hh.trans (hdrep x)
  have hh := continuous_eq_on_measure_support (quotientMeasure N) _ _
    (hc.inner continuous_const) (hK x) he hx
  have hn : inner ℂ (c x) (c x)=((‖c x‖^2 : ℝ):ℂ) := by
    rw [inner_self_eq_norm_sq_to_K,Complex.ofReal_pow]
    rfl
  exact hn.symm.trans hh

/-- The radial lift inherits the exact time support radius. -/
theorem evenCoshLift_support_of_time_support (f : ℝ → ℂ) (R : ℝ) (hR : 0≤R)
    (hs : Function.support f⊆Icc (-R) R) :
    Function.support (evenCoshLift f)⊆Iic (Real.cosh R) := by
  intro q hq
  by_contra hn
  exact hq (evenCoshLift_zero_above f R hR hs q (lt_of_not_ge hn))

/-- The original compact real even packet has exactly the time-convolution
Abel kernel on its square-energy diagonal, for every point in quotient support. -/
theorem timeSquare_kernel_diagonal_on_support (N : ℕ) [NeZero N]
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (x : ℍ) (hx : x∈(quotientMeasure N).support) :
    ((∫ y,‖radialPoincareKernel N (abelProfile (evenCoshLift f)) x y‖^2
      ∂quotientMeasure N : ℝ):ℂ)=
      radialPoincareKernel N (abelProfile (evenCoshLift (timeConvolution f f))) x x := by
  let F := evenCoshLift f
  have hF : ContDiffOn ℝ ∞ F (Ici 1) := evenCoshLift_smoothOn f (f.smooth ⊤) he hc
  have hsF : Function.support F⊆Iic (Real.cosh R) :=
    evenCoshLift_support_of_time_support f R hR hs
  let g := timeConvolution f f
  have hgc : HasCompactSupport (g : ℝ → ℂ) := timeConvolution_compact f f hc hc
  have hge : Function.Even g := timeConvolution_even f f he he
  have hgr : ∀ t,star (g t)=g t := timeConvolution_real f f hr hr
  have hgs : Function.support g⊆Icc (-(R+R)) (R+R) := timeConvolution_support f f R R hs hs
  let G := evenCoshLift g
  have hG : ContDiffOn ℝ ∞ G (Ici 1) := evenCoshLift_smoothOn g (g.smooth ⊤) hge hgc
  have hsG : Function.support G⊆Iic (Real.cosh (R+R)) :=
    evenCoshLift_support_of_time_support g (R+R) (add_nonneg hR hR) hgs
  let c := oneSidedAbelColumn N F hF R hR hsF
  let d := oneSidedAbelColumn N G hG (R+R) (add_nonneg hR hR) hsG
  let A := Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f (f.smooth ⊤) hc)
  have hAc (v : AutomorphicSpace N) : (A v).val=ᵐ[quotientMeasure N]
      (fun z => inner ℂ (c z) v) := by
    simp_rw [c,oneSidedAbelColumn_inner N F hF (evenCoshLift_real f hr) R hR hsF]
    exact evenWavePacket_kernel_coeFn N f (f.smooth ⊤) he hc hr R hR hs v
  have hAd (v : AutomorphicSpace N) : (A (A v)).val=ᵐ[quotientMeasure N]
      (fun z => inner ℂ (d z) v) := by
    simp_rw [d,oneSidedAbelColumn_inner N G hG (evenCoshLift_real g hgr)
      (R+R) (add_nonneg hR hR) hsG]
    exact timeConvolution_wavePacket_kernel N f f hc hc he he hr hr R R hR hR hs hs v
  have hcont : Continuous (fun p : ℍ×ℍ => radialPoincareKernel N (abelProfile G) p.1 p.2) :=
    oneSidedAbelKernel_joint_continuous N G hG (R+R) (add_nonneg hR hR) hsG
  have hh := selfAdjoint_kernel_square_diagonal N A
    (Wave.shiftedQuotientWavePacket_isSelfAdjoint N f _ hr) c d
    (oneSidedAbelColumn_continuous N F hF R hR hsF)
    (oneSidedAbelColumn_continuous N G hG (R+R) (add_nonneg hR hR) hsG)
    (radialPoincareKernel N (abelProfile G))
    (fun z => Continuous.uncurry_left (f:=radialPoincareKernel N (abelProfile G)) z hcont) hAc hAd
    (oneSidedAbelColumn_coeFn N G hG (R+R) (add_nonneg hR hR) hsG) x hx
  simpa only [c,oneSidedAbelColumn_energy N F hF R hR hsF] using hh

/-- Almost every centre lies in the measure support, so the diagonal identity
holds almost everywhere on the quotient. No restriction of a product-AE identity is used. -/
theorem timeSquare_kernel_diagonal_ae (N : ℕ) [NeZero N]
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    ∀ᵐ x ∂quotientMeasure N,
      ((∫ y,‖radialPoincareKernel N (abelProfile (evenCoshLift f)) x y‖^2
        ∂quotientMeasure N : ℝ):ℂ)=
        radialPoincareKernel N (abelProfile (evenCoshLift (timeConvolution f f))) x x := by
  filter_upwards [Measure.support_mem_ae (μ:=quotientMeasure N)] with x hx
  exact timeSquare_kernel_diagonal_on_support N f hc he hr R hR hs x hx

/-- Pretrace with the literal convolution-kernel diagonal, for the original
compact even time packet on a full quotient Hilbert basis. -/
theorem timeSquare_kernel_pretrace {ι : Type*} [Countable ι] (N : ℕ) [NeZero N]
    (b : HilbertBasis ι ℂ (AutomorphicSpace N))
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    ∀ᵐ x ∂quotientMeasure N,
      HasSum (fun i => ‖(Wave.shiftedQuotientWavePacket N f
        (compactSmoothWaveWeight f (f.smooth ⊤) hc) (b i)).val x‖^2)
        (radialPoincareKernel N (abelProfile (evenCoshLift (timeConvolution f f))) x x).re := by
  filter_upwards [evenWavePacket_pretrace N b f (f.smooth ⊤) he hc hr R hR hs,
    timeSquare_kernel_diagonal_ae N f hc he hr R hR hs] with x hx hd
  have hh := congrArg Complex.re hd
  simp only [Complex.ofReal_re] at hh
  rwa [hh] at hx

/-- The actual moving-window packet has the literal convolution-kernel
square-energy diagonal without an externally supplied support radius. -/
theorem windowTimeSquare_kernel_diagonal (N : ℕ) [NeZero N] (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) :
    ∀ᵐ x ∂quotientMeasure N,
      ((∫ y,‖radialPoincareKernel N
        (abelProfile (evenCoshLift (windowTimeSchwartz K hc R hR a b))) x y‖^2
        ∂quotientMeasure N : ℝ):ℂ)=
      radialPoincareKernel N (abelProfile (evenCoshLift
        (timeConvolution (windowTimeSchwartz K hc R hR a b)
          (windowTimeSchwartz K hc R hR a b)))) x x := by
  obtain ⟨B,hB,hs⟩ := symmetricWindowTimeTest_uniform_support K hc
  exact timeSquare_kernel_diagonal_ae N (windowTimeSchwartz K hc R hR a b)
    (symmetricWindowTimeTest_compact K hc R a b hR)
    (symmetricWindowTimeTest_even K he R a b)
    (symmetricWindowTimeTest_real K he R a b) (B*R) (mul_nonneg hB.le hR.le) (hs R hR a b)

#print axioms timeSquare_kernel_pretrace
#print axioms windowTimeSquare_kernel_diagonal
#print axioms selfAdjoint_kernel_square_diagonal
#print axioms evenCoshLift_support_of_time_support
#print axioms timeSquare_kernel_diagonal_on_support
#print axioms timeSquare_kernel_diagonal_ae

end QuantitativeMaass
