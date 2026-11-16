module

public import QuantitativeMaassPacketCrossKernelV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace SchwartzMap

namespace QuantitativeMaass

/-- The actual even/odd projection for sigma equal to +1 or -1. -/
def parityProjection (N : ℕ) (σ : ℝ) : AutomorphicSpace N →L[ℂ] AutomorphicSpace N :=
  (1/2:ℂ) • (1+(σ:ℂ) • (reflectionIsometry N).toContinuousLinearMap)

theorem parityProjection_apply (N : ℕ) (σ : ℝ) (v : AutomorphicSpace N) :
    parityProjection N σ v=(1/2:ℂ) • (v+(σ:ℂ) • reflectionIsometry N v) := rfl

theorem parityProjection_selfAdjoint (N : ℕ) (σ : ℝ) : IsSelfAdjoint (parityProjection N σ) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change inner ℂ (parityProjection N σ x) y=inner ℂ x (parityProjection N σ y)
  have hu : inner ℂ (reflectionIsometry N x) y=inner ℂ x (reflectionIsometry N y) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (reflectionIsometry_selfAdjoint N) x y
  rw [parityProjection_apply,parityProjection_apply]
  have hl := @inner_smul_left ℂ (AutomorphicSpace N) _ _ _
    (x+(σ:ℂ) • reflectionIsometry N x) y (1/2:ℂ)
  have hr := @inner_smul_right ℂ (AutomorphicSpace N) _ _ _
    x (y+(σ:ℂ) • reflectionIsometry N y) (1/2:ℂ)
  rw [hl,hr,inner_add_left,inner_add_right,
    inner_smul_left (reflectionIsometry N x) y (σ:ℂ),
    inner_smul_right x (reflectionIsometry N y) (σ:ℂ)]
  simp only [map_div₀,map_one,map_ofNat,Complex.conj_ofReal,hu]

/-- The range lies in the genuine sigma eigenspace of the geometric reflection. -/
theorem parityProjection_eigen (N : ℕ) (σ : ℝ) (hσ : σ^2=1) (v : AutomorphicSpace N) :
    reflectionIsometry N (parityProjection N σ v)=(σ:ℂ) • parityProjection N σ v := by
  rw [parityProjection_apply,map_smul,map_add,map_smul,reflectionIsometry_involutive]
  rcases sq_eq_one_iff.mp hσ with h | h
  · subst σ
    simp [add_comm]
  · subst σ
    simp
    module

theorem parityProjection_idempotent (N : ℕ) (σ : ℝ) (hσ : σ^2=1) (v : AutomorphicSpace N) :
    parityProjection N σ (parityProjection N σ v)=parityProjection N σ v := by
  rw [parityProjection_apply,parityProjection_eigen N σ hσ,smul_smul]
  have hh : (σ:ℂ)*(σ:ℂ)=1 := by exact_mod_cast (by nlinarith [hσ] : σ*σ=1)
  rw [hh,one_smul]
  module

/-- Squared norm of the actual parity projection, with its reflection cross term. -/
theorem parityProjection_energy (N : ℕ) (σ : ℝ) (hσ : σ^2=1) (v : AutomorphicSpace N) :
    ((‖parityProjection N σ v‖^2:ℝ):ℂ)=
      (inner ℂ v v+(σ:ℂ)*inner ℂ (reflectionIsometry N v) v)/2 := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (parityProjection_selfAdjoint N σ)
  have hu := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (reflectionIsometry_selfAdjoint N)
  have he : inner ℂ (parityProjection N σ v) (parityProjection N σ v)=
      inner ℂ v (parityProjection N σ (parityProjection N σ v)) := hs v (parityProjection N σ v)
  rw [parityProjection_idempotent N σ hσ] at he
  have hn : inner ℂ (parityProjection N σ v) (parityProjection N σ v)=
      ((‖parityProjection N σ v‖^2:ℝ):ℂ) := by
    rw [inner_self_eq_norm_sq_to_K,Complex.ofReal_pow]
    rfl
  have huu : inner ℂ (reflectionIsometry N v) v=inner ℂ v (reflectionIsometry N v) := hu v v
  rw [← hn,he,parityProjection_apply,
    inner_smul_right v (v+(σ:ℂ) • reflectionIsometry N v) (1/2:ℂ),inner_add_right,
    inner_smul_right v (reflectionIsometry N v) (σ:ℂ),← huu]
  ring

/-- Literal parity-column energy equals one half of the original diagonal
plus the signed reflected kernel. This is valid at every centre. -/
theorem timeSquare_parity_energy (N : ℕ) [NeZero N] (σ : ℝ) (hσ : σ^2=1)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) (x : ℍ) :
    ((‖parityProjection N σ (timeAbelColumn N f hc he R hR hs x)‖^2:ℝ):ℂ)=
      (radialPoincareKernel N (abelProfile (evenCoshLift (timeConvolution f f))) x x+
        (σ:ℂ)*radialPoincareKernel N (abelProfile (evenCoshLift (timeConvolution f f))) x (J•x))/2 := by
  rw [parityProjection_energy N σ hσ]
  have hj : reflectionIsometry N (timeAbelColumn N f hc he R hR hs x)=
      timeAbelColumn N f hc he R hR hs (J•x) := reflectionIsometry_abelColumn N _ _ _ _ _ x
  rw [hj,timeSquare_kernel_cross N f hc he hr R hR hs x x,
    timeSquare_kernel_cross N f hc he hr R hR hs x (J•x)]

/-- Actual parity-projected wave-packet pretrace over any full quotient
Hilbert basis. All geometric diagonal and reflection terms are literal kernels. -/
theorem timeSquare_parity_pretrace {ι : Type*} [Countable ι] (N : ℕ) [NeZero N]
    (b : HilbertBasis ι ℂ (AutomorphicSpace N)) (σ : ℝ) (hσ : σ^2=1)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    ∀ᵐ x ∂quotientMeasure N,
      HasSum (fun i => ‖(Wave.shiftedQuotientWavePacket N f
        (compactSmoothWaveWeight f (f.smooth ⊤) hc) (parityProjection N σ (b i))).val x‖^2)
        (((radialPoincareKernel N (abelProfile (evenCoshLift (timeConvolution f f))) x x).re+
          σ*(radialPoincareKernel N (abelProfile (evenCoshLift (timeConvolution f f))) x (J•x)).re)/2) := by
  let c := timeAbelColumn N f hc he R hR hs
  have hrep (i : ι) :
      (Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f (f.smooth ⊤) hc)
        (parityProjection N σ (b i))).val=ᵐ[quotientMeasure N]
        (fun x => inner ℂ (c x) (parityProjection N σ (b i))) := by
    simp_rw [c,timeAbelColumn,oneSidedAbelColumn_inner N _ _ (evenCoshLift_real f hr)]
    exact evenWavePacket_kernel_coeFn N f (f.smooth ⊤) he hc hr R hR hs _
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (parityProjection_selfAdjoint N σ)
  filter_upwards [ae_all_iff.mpr hrep] with x hx
  have hp := hasSum_inner_norm_sq b (parityProjection N σ (c x))
  have hh (u v : AutomorphicSpace N) : inner ℂ (parityProjection N σ u) v=
      inner ℂ u (parityProjection N σ v) := hsym u v
  simp_rw [hh] at hp
  simp_rw [hx]
  have heq := congrArg Complex.re (timeSquare_parity_energy N σ hσ f hc he hr R hR hs x)
  norm_num only [Complex.ofReal_re,Complex.div_ofNat_re,Complex.add_re,Complex.mul_re,
    Complex.ofReal_im,zero_mul,sub_zero] at heq
  rw [← heq]
  exact hp

#print axioms parityProjection_apply
#print axioms parityProjection_selfAdjoint
#print axioms parityProjection_eigen
#print axioms parityProjection_idempotent
#print axioms parityProjection_energy
#print axioms timeSquare_parity_energy
#print axioms timeSquare_parity_pretrace

end QuantitativeMaass
