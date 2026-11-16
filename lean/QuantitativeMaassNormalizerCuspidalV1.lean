module

public import QuantitativeMaassRationalCuspChartV1
public import QuantitativeNinaMaassOldSpectrumV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson QuantitativeNinaMaass
open AsymptoticCongruenceLabels AsymptoticClassicalCusp AsymptoticClassicalDiscriminant
open scoped MatrixGroups
namespace QuantitativeMaass

/-- The literal cusp profile after any rational normalizer has rational
slope and shift, with the actual level period retained. -/
theorem normalizer_cusp_coordinates (N : ℕ) (hN : 0<N)
    (g : quotientNormalizerGroup N) (s U : SL(2,ℤ)) (a b d : ℤ) (ha : 0<a) (hd : 0<d)
    (he : ∀ z : ℍ,g.val • (s • z)=U • affine ((a:ℝ)/d)
      (div_pos (by exact_mod_cast ha) (by exact_mod_cast hd)) ((b:ℝ)/d) z)
    (f : ℍ → ℂ) (x y : ℝ) (hy : 0<y) :
    cuspProfile N s (fun z => f (g.val • z)) x y=
      cuspProfile N U f ((a:ℝ)/d*x+(b:ℝ)/d/N) ((a:ℝ)/d*y) := by
  have haR : (0:ℝ)<a := by exact_mod_cast ha
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hNy : 0<(a:ℝ)/d*y := mul_pos (div_pos haR hdR) hy
  simp only [cuspProfile,dite_eq_left hy,dite_eq_left hNy]
  change f (g.val • (s • horocyclePoint ((N:ℝ)*x) y hy))=
    f (U • horocyclePoint ((N:ℝ)*((a:ℝ)/d*x+(b:ℝ)/d/N)) ((a:ℝ)/d*y) hNy)
  rw [he]
  congr 1
  congr 1
  apply UpperHalfPlane.ext
  apply Complex.ext
  · simp only [affine,horocyclePoint,Complex.add_re,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    have hNR : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
    field_simp
  · simp only [affine,horocyclePoint,Complex.add_im,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]

/-- Every rational quotient normalizer preserves literal vanishing cusp constants. -/
theorem normalizerRepresentative_constant_zero (N : ℕ) (hN : 0<N)
    (g : quotientNormalizerGroup N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val)
    (hzero : ∀ s : SL(2,ℤ),∀ y : ℝ,0<y → cuspConstant N s f.val y=0)
    (s : SL(2,ℤ)) (y : ℝ) (hy : 0<y) :
    cuspConstant N s (quotientNormalizerRepresentative N g f).val y=0 := by
  obtain ⟨U,a,b,d,ha,hd,he⟩ := rational_cusp_affine_chart g.val s
  have haR : (0:ℝ)<a := by exact_mod_cast ha
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hcoord : (fun x => cuspProfile N s (quotientNormalizerRepresentative N g f).val x y)=
      fun x => cuspProfile N U f.val ((a:ℝ)/d*x+(b:ℝ)/d/N) ((a:ℝ)/d*y) := by
    funext x
    exact normalizer_cusp_coordinates N hN g s U a b d ha hd he f.val x y hy
  have hp := cuspProfile_periodic N s (quotientNormalizerRepresentative N g f).val
    (quotientNormalizerRepresentative N g f).property.2.1 y
  rw [hcoord] at hp
  unfold cuspConstant zeroFourier
  rw [hcoord]
  rw [periodic_mean_rational_affine _
    (cuspProfile_continuous N U f.val hf ((a:ℝ)/d*y))
    (cuspProfile_periodic N U f.val f.property.2.1 ((a:ℝ)/d*y))
    a d ha.ne' hd.ne' ((b:ℝ)/d/N) hp]
  exact hzero U ((a:ℝ)/d*y) (mul_pos (div_pos haR hdR) hy)

/-- Cuspidality is preserved on the actual completed quotient space by
every rational normalizer. -/
theorem quotientNormalizerPullback_mem_cuspidal (N : ℕ) (hN : 0<N)
    (g : quotientNormalizerGroup N) (x : AutomorphicSpace N)
    (hx : x∈localCuspidalSpace N hN) :
    quotientNormalizerPullback N g x∈localCuspidalSpace N hN := by
  apply cuspidal_operator_mem_of_continuous N N hN hN
    (quotientNormalizerPullback N g).toContinuousLinearMap _ x hx
  intro f hf hcusp
  change quotientNormalizerPullback N g (AutomorphicL2.denseEmbedding _ _ f)∈localCuspidalSpace N hN
  rw [quotientNormalizerPullback_representative]
  have hcont : Continuous (quotientNormalizerRepresentative N g f).val := by
    change Continuous (fun z => f.val (g.val • z))
    exact hf.comp (AsymptoticRationalBranches.action_continuous g.val)
  apply continuous_representative_mem_cuspidal N hN (quotientNormalizerRepresentative N g f) hcont
  apply normalizerRepresentative_constant_zero N hN g f hf
  intro s y hy
  exact localCuspidalSpace_continuous_constant_zero N hN _ hcusp f.val hf
    f.property.2.1 f.property.2.2.coeFn_toLp s y hy

#print axioms normalizer_cusp_coordinates
#print axioms normalizerRepresentative_constant_zero
#print axioms quotientNormalizerPullback_mem_cuspidal
end QuantitativeMaass
