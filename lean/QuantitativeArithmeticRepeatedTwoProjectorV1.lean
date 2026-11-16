module

public import QuantitativeArithmeticRepeatedTwoPhysicalV1
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
@[expose] public noncomputable section

open Polynomial QuantitativeMaass QuantitativeNinaMaass
open QuantitativeArithmeticRepeatedTwoPhysical
open scoped InnerProductSpace

namespace QuantitativeArithmeticRepeatedTwoProjector

/-- The square-product case has a cubic identity, with no repeated root. -/
theorem square_product_cubic {R : Type*} [Ring R] (U V : R)
    (hU : U*U=1) (hV : V*V=1) (hUV : (U*V)^2=1) :
    (U+V)^3-4*(U+V)=0 := by
  have hUU (x : R) : U*(U*x)=x := by rw [←mul_assoc,hU,one_mul]
  have hVV (x : R) : V*(V*x)=x := by rw [←mul_assoc,hV,one_mul]
  have hfour : U*(V*(U*V))=1 := by simpa only [pow_two,mul_assoc] using hUV
  have hc := congrArg (fun x => U*(x*V)) hfour
  simp only [mul_assoc,hUU,hV,mul_one,one_mul] at hc
  have hVU (x : R) : V*(U*x)=U*(V*x) := by rw [←mul_assoc,hc,mul_assoc]
  noncomm_ring [hUU,hVV,hU,hV,hVU,hc]

theorem sum_two_reflections {R : Type*} [Ring R] (D W : R) (hW : W*W=1) :
    (D-1)+W*((D-1)*W)+2=D+W*(D*W) := by
  noncomm_ring [hW]
  simp only [zsmul_one, Int.cast_neg, Int.cast_ofNat]
  abel

def annihilator : ℂ[X] := X^5-5*X^3+4*X

/-- The unique degree-four polynomial equal to one at -2 and zero at
-1,0,1,2. These are all possible eigenvalues of the two-reflection sum. -/
def projectorPolynomial : ℂ[X] :=
  C (1/24) * (X^4-C 2*X^3-X^2+C 2*X)

theorem polynomial_identity :
    (X+2)*projectorPolynomial = C (1/24)*annihilator := by
  unfold projectorPolynomial annihilator
  simp only [map_ofNat]
  ring

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def projector (A : E →L[ℂ] E) : E →L[ℂ] E := aeval A projectorPolynomial

omit [CompleteSpace E] in
theorem projector_formula (A : E →L[ℂ] E) :
    projector A = (1/24 : ℂ) • (A^4-(2:ℂ) • A^3-A^2+(2:ℂ) • A) := by
  simp [projector, projectorPolynomial, Algebra.algebraMap_eq_smul_one ]

theorem projector_selfAdjoint (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (projector A) := by
  rw [projector_formula]
  apply IsSelfAdjoint.smul (show IsSelfAdjoint (1/24:ℂ) by simp [IsSelfAdjoint])
  exact (((hA.pow 4).sub (IsSelfAdjoint.smul (by simp [IsSelfAdjoint]) (hA.pow 3))).sub
    (hA.pow 2)).add (IsSelfAdjoint.smul (by simp [IsSelfAdjoint]) hA)

omit [CompleteSpace E] in
theorem projector_range (A : E →L[ℂ] E) (h : aeval A annihilator=0) :
    (A+2)*projector A=0 := by
  have he := congrArg (aeval A) polynomial_identity
  simpa only [map_mul, map_add, Polynomial.aeval_X, map_ofNat, h, mul_zero, projector] using he

omit [CompleteSpace E] in
theorem projector_fixed (A : E →L[ℂ] E) (x : E) (hx : (A+2) x=0) :
    projector A x=x := by
  have ha : A x=(-2:ℂ) • x := by
    have hx : A x + (2:ℂ) • x = 0 := by
      simpa only [add_apply, ContinuousLinearMap.ofNat_apply, two_smul] using hx
    apply eq_neg_of_add_eq_zero_left at hx
    simpa using hx
  rw [projector_formula]
  simp [pow_succ, mul_apply_eq_comp, ha, map_smul, smul_smul]
  module

/-- The finite polynomial is exactly the orthogonal projection, on the
whole Hilbert space, without a finite-dimensionality hypothesis. -/
theorem projector_eq_starProjection (A : E →L[ℂ] E) (hA : IsSelfAdjoint A)
    (h : aeval A annihilator=0) : projector A=(A+2).ker.starProjection := by
  ext x
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact DFunLike.congr_fun (projector_range A h) x
  · intro w hw
    have hs : inner ℂ (projector A x) w = inner ℂ x (projector A w) :=
      ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (projector_selfAdjoint A hA) x w
    rw [inner_sub_left, hs, projector_fixed A w hw, sub_self]

end Hilbert

def reflectionSum (L : ℕ) (hL : 0<L) [NeZero (2*(2*L))] :=
  ordinaryOperator L + conjugateOperator L hL

theorem even_cubic (t : ℕ) (ht : 0<t) [NeZero (2*(2*(2*t)))] :
    (reflectionSum (2*t) (by omega))^3 - 4*reflectionSum (2*t) (by omega)=0 := by
  apply square_product_cubic (ordinaryOperator (2*t)) (conjugateOperator (2*t) (by omega))
    (ordinary_square (2*t) (by omega)) (conjugate_square (2*t) (by omega))
  exact power_eq_one _ _ (product_embedding (2*t) (by omega)) 2
    (QuantitativeArithmeticRepeatedTwoTrace.even_product t ht)

theorem reflectionSum_annihilator (L : ℕ) (hL : 0<L) [NeZero (2*(2*L))] :
    aeval (reflectionSum L hL) annihilator=0 := by
  rcases Nat.even_or_odd L with he | ho
  · obtain ⟨t,he⟩ := he
    rw [←two_mul] at he
    subst L
    have ht : 0<t := by omega
    have hp : annihilator=(X^2-1)*(X^3-4*X) := by unfold annihilator; ring
    rw [hp, map_mul]
    have hc : aeval (reflectionSum (2*t) hL) (X^3-4*X : ℂ[X])=0 := by
      simpa only [map_sub,map_mul,map_pow,Polynomial.aeval_X,map_ofNat] using even_cubic t ht
    rw [hc,mul_zero]
  · obtain ⟨t,rfl⟩ := ho
    have hp : annihilator=X*(X^4-5*X^2+4) := by unfold annihilator; ring
    rw [hp,map_mul]
    have hc : aeval (reflectionSum (2*t+1) hL) (X^4-5*X^2+4 : ℂ[X])=0 := by
      simpa only [map_sub,map_add,map_mul,map_pow,Polynomial.aeval_X,map_ofNat,reflectionSum] using odd_annihilator t
    rw [hc,mul_zero]

theorem ordinary_selfAdjoint (L : ℕ) [NeZero (2*(2*L))] :
    IsSelfAdjoint (ordinaryOperator L) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  simp [ordinaryOperator, levelTrace, ContinuousLinearMap.adjoint_comp]

theorem reflectionSum_selfAdjoint (L : ℕ) (hL : 0<L) [NeZero (2*(2*L))] :
    IsSelfAdjoint (reflectionSum L hL) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  simp only [reflectionSum, map_add, conjugateOperator, ContinuousLinearMap.adjoint_comp,
    (ordinary_selfAdjoint L).adjoint_eq,
    (frickeIsometry_selfAdjoint (2*(2*L)) (by omega)).adjoint_eq,
    ContinuousLinearMap.comp_assoc]

/-- An exact degree-four finite-word projector for every repeated factor 2. -/
theorem physical_projector (L : ℕ) (hL : 0<L) [NeZero (2*(2*L))] :
    projector (reflectionSum L hL)=(reflectionSum L hL+2).ker.starProjection :=
  projector_eq_starProjection _ (reflectionSum_selfAdjoint L hL) (reflectionSum_annihilator L hL)

/-- A sum of two physical Gram operators detects exactly the two kernels. -/
theorem sum_gram_kernel {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (T B : E →L[ℂ] F) :
    (T.adjoint.comp T+B.adjoint.comp B).ker=T.ker ⊓ B.ker := by
  ext x
  constructor
  · intro hx
    change T.adjoint (T x)+B.adjoint (B x)=0 at hx
    have hi : inner ℂ (T.adjoint (T x)+B.adjoint (B x)) x=0 := by rw [hx,inner_zero_left]
    rw [inner_add_left,ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_left] at hi
    have hr := congrArg Complex.re hi
    simp only [Complex.add_re,Complex.zero_re] at hr
    have htn : (inner ℂ (T x) (T x)).re=‖T x‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) (T x)
    have hbn : (inner ℂ (B x) (B x)).re=‖B x‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) (B x)
    rw [htn,hbn] at hr
    have ht : ‖T x‖=0 := by nlinarith [sq_nonneg ‖B x‖,norm_nonneg (T x)]
    have hb : ‖B x‖=0 := by nlinarith [sq_nonneg ‖T x‖,norm_nonneg (B x)]
    exact ⟨norm_eq_zero.mp ht,norm_eq_zero.mp hb⟩
  · rintro ⟨ht,hb⟩
    change T x=0 at ht
    change B x=0 at hb
    change T.adjoint (T x)+B.adjoint (B x)=0
    rw [ht,hb,map_zero,map_zero,add_zero]

theorem physical_kernel (L : ℕ) (hL : 0<L) [NeZero (2*(2*L))] :
    (reflectionSum L hL+2).ker =
      newTraceKernel (show 0<2*(2*L) by omega) (Nat.dvd_mul_left (2*L) 2) := by
  let T := levelTrace (Nat.dvd_mul_left (2*L) 2)
  let W := (frickeIsometry (2*(2*L)) (by omega)).toContinuousLinearMap
  have hw : W*W=1 := by
    apply ContinuousLinearMap.ext
    intro x
    exact frickeIsometry_involutive (2*(2*L)) (by omega) x
  have ht : T.adjoint=levelCover (Nat.dvd_mul_left (2*L) 2) := by simp [T,levelTrace]
  have he : reflectionSum L hL+2=T.adjoint.comp T+(T.comp W).adjoint.comp (T.comp W) := by
    rw [ContinuousLinearMap.adjoint_comp,ht,
      (frickeIsometry_selfAdjoint (2*(2*L)) (by omega)).adjoint_eq]
    change (levelCover (Nat.dvd_mul_left (2*L) 2) ∘L T-1)+
      W*((levelCover (Nat.dvd_mul_left (2*L) 2) ∘L T-1)*W)+2 =
      (levelCover (Nat.dvd_mul_left (2*L) 2) ∘L T)+
        W*((levelCover (Nat.dvd_mul_left (2*L) 2) ∘L T)*W)
    exact sum_two_reflections _ W hw
  rw [he,sum_gram_kernel]
  rfl

local instance {M N : ℕ} [NeZero N] (hN : 0<N) (hMN : M∣N) :
    (newTraceKernel hN hMN).HasOrthogonalProjection := by
  rw [newTraceKernel_eq_orthogonal]
  infer_instance

/-- The exact projector onto the ordinary and Fricke trace kernels,
with zero approximation error and no exceptional spectral space. -/
theorem common_trace_projector (L : ℕ) (hL : 0<L) [NeZero (2*(2*L))] :
    projector (reflectionSum L hL)=
      (newTraceKernel (show 0<2*(2*L) by omega) (Nat.dvd_mul_left (2*L) 2)).starProjection := by
  simpa only [physical_kernel L hL] using physical_projector L hL

#print axioms square_product_cubic
#print axioms projector_eq_starProjection
#print axioms reflectionSum_annihilator
#print axioms physical_projector
#print axioms physical_kernel
#print axioms common_trace_projector

end QuantitativeArithmeticRepeatedTwoProjector
