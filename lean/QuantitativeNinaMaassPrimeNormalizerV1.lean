module

public import QuantitativeNinaMaassHeckeOperatorsV1
public import QuantitativeNinaMaassTraceDiamondsV1
public import QuantitativeArithmeticMaassHeckeTheoryV4

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane Matrix QuantitativeMaass
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open AsymptoticClassicalCusp AsymptoticCongruenceLabels AsymptoticClassicalDiscriminant
open QuantitativeArithmeticMaassHecke
open scoped Topology MatrixGroups InnerProductSpace

/-!
Reuse the existing actual determinant-p Hilbert normalizer at level p*M.
The transformed compact Poincare seed proves preservation of the full
Friedrichs graph. This is the local Atkin--Lehner operator needed at a
simply ramified prime; its identification with the normalized upper-branch
operator on the newspace is a separate subsequent step.
-/

namespace QuantitativeNinaMaass

def primeNormalizerRepresentative (M p : ℕ) [Fact p.Prime]
    (hM : 0 < M) (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1) :
    AutomorphicL2.representatives (gamma (p * M)) (quotientMeasure (p * M)) →ₗ[ℂ]
      AutomorphicL2.representatives (gamma (p * M)) (quotientMeasure (p * M)) :=
  AutomorphicL2.normalizerRepresentative volume AsymptoticRationalGroup.measurePreserving
    (gamma (p * M)) (heckeNormalizerLabel M p (Fact.out : p.Prime).pos A B hAB)
    (fun _ ha => heckeNormalizer_conj_mem M p (Fact.out : p.Prime).pos A B hAB hM ha)
    (fun _ ha => heckeNormalizer_inv_conj_mem M p (Fact.out : p.Prime).pos A B hAB hM ha)
    (density (p * M)) (density_measurable (p * M)) (density_orbit_sum (p * M))

theorem primeNormalizer_apply (M p : ℕ) [Fact p.Prime]
    (hM : 0 < M) (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1)
    (f : AutomorphicL2.representatives (gamma (p * M)) (quotientMeasure (p * M))) :
    HeckeL2.normalizer M p hM A B hAB (AutomorphicL2.denseEmbedding _ _ f) =
      AutomorphicL2.denseEmbedding _ _ (primeNormalizerRepresentative M p hM A B hAB f) :=
  AutomorphicL2.normalizerIsometry_apply volume AsymptoticRationalGroup.measurePreserving
    (gamma (p * M)) (heckeNormalizerLabel M p (Fact.out : p.Prime).pos A B hAB)
    _ _ (density (p * M)) (density_measurable (p * M)) (density_orbit_sum (p * M)) f

theorem primeNormalizerRepresentative_continuous (M p : ℕ) [Fact p.Prime]
    (hM : 0 < M) (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1)
    (f : AutomorphicL2.representatives (gamma (p * M)) (quotientMeasure (p * M)))
    (hf : Continuous f.val) :
    Continuous (primeNormalizerRepresentative M p hM A B hAB f).val :=
  hf.comp (AsymptoticRationalBranches.action_continuous _)

theorem primeNormalizer_involutive (M p : ℕ) [Fact p.Prime]
    (hM : 0 < M) (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1) :
    Function.Involutive (HeckeL2.normalizer M p hM A B hAB) := by
  apply AutomorphicL2.normalizerIsometry_involutive
  rw [heckeNormalizerLabel_eq M p (Fact.out : p.Prime).pos A B hAB hM]
  simpa only [_root_.mul_inv_rev] using (gamma (p * M)).inv_mem
    (AsymptoticAtkinLehner.localAtkin_square_mem M p hM (Fact.out : p.Prime).pos A B hAB)

/-- The exact compact test pulled back through the inverse normalizer. -/
def primeNormalizerSeed (M p : ℕ) (hp : 0 < p)
    (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1) (u : SmoothUpperSeed) :
    SmoothUpperSeed :=
  (affineSeed u (1 / (p : ℝ)) 0 (by positivity)).cuspPush (heckeSL M p A B hAB)⁻¹

theorem inverse_affine_dilation (p : ℕ) (hp : 0 < p) (z : ℍ) :
    affine (1 / (p : ℝ)) (by positivity) 0 (dilationReal p hp • z) = z := by
  rw [dilation_action]
  apply UpperHalfPlane.ext
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  simp only [affine, Complex.ofReal_zero, add_zero, Complex.ofReal_div, Complex.ofReal_one]
  rw [← mul_assoc]
  simp only [Complex.ofReal_natCast, one_div, inv_mul_cancel₀ hpC, one_mul]

theorem primeNormalizerSeed_cancel (M p : ℕ) (hp : 0 < p)
    (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1) (u : SmoothUpperSeed) (z : ℍ) :
    upperFunction (primeNormalizerSeed M p hp A B hAB u).toFun
      (heckeNormalizerLabel M p hp A B hAB • z) = upperFunction u.toFun z := by
  have hcancel : cuspAction (heckeSL M p A B hAB)
      (heckeNormalizerLabel M p hp A B hAB • z) = dilationReal p hp • z := by
    rw [← heckeNormalizer_action]
    simp only [cuspAction, heckeNormalizerReal, mul_smul, map_inv, smul_inv_smul]
  change upperFunction ((affineSeed u (1 / (p : ℝ)) 0 (by positivity)).toFun ∘
    integralCuspChart ((heckeSL M p A B hAB)⁻¹)⁻¹) _ = _
  rw [inv_inv, upperFunction_cuspChart, hcancel]
  change upperFunction (u.toFun ∘ affineChart (1 / (p : ℝ)) 0)
    (dilationReal p hp • z) = _
  rw [upperFunction_affine u.toFun (1 / (p : ℝ)) 0 (by positivity),
    Function.comp_apply, triangularGL_action]
  simp only [div_one]
  rw [inverse_affine_dilation]

theorem primeNormalizerSeed_laplacian (N M p : ℕ) (hp : 0 < p)
    (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1) (u : SmoothUpperSeed) :
    poincareSeedVector N (primeNormalizerSeed M p hp A B hAB u).laplacian =
      poincareSeedVector N (primeNormalizerSeed M p hp A B hAB u.laplacian) := by
  unfold primeNormalizerSeed
  rw [poincare_cuspPush_laplacian]
  apply poincareSeedVector_congr
  funext z
  change upperFunction ((affineSeed u (1 / (p : ℝ)) 0 (by positivity)).laplacian.toFun ∘
      integralCuspChart ((heckeSL M p A B hAB)⁻¹)⁻¹) z =
    upperFunction ((affineSeed u.laplacian (1 / (p : ℝ)) 0 (by positivity)).toFun ∘
      integralCuspChart ((heckeSL M p A B hAB)⁻¹)⁻¹) z
  rw [upperFunction_cuspChart, upperFunction_cuspChart]
  exact congrFun (affineSeed_laplacian u (1 / (p : ℝ)) 0 (by positivity)) _

theorem primeNormalizer_seed_pairing (M p : ℕ) (hp : 0 < p)
    (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1)
    (u : SmoothUpperSeed) (f : ℍ → ℂ) :
    (∫ z : ℍ, star (upperFunction u.toFun z) * f (heckeNormalizerLabel M p hp A B hAB • z)) =
      ∫ z : ℍ, star (upperFunction (primeNormalizerSeed M p hp A B hAB u).toFun z) * f z := by
  let : ContinuousConstSMul AsymptoticRationalGroup.Group ℍ :=
    ⟨AsymptoticRationalBranches.action_continuous⟩
  have h := (AsymptoticRationalGroup.measurePreserving
    (heckeNormalizerLabel M p hp A B hAB)).integral_comp
    (Homeomorph.smul (heckeNormalizerLabel M p hp A B hAB)).measurableEmbedding
    (fun z => star (upperFunction (primeNormalizerSeed M p hp A B hAB u).toFun z) * f z)
  simpa only [primeNormalizerSeed_cancel] using h

theorem poincareSeed_pairing_primeNormalizer (M p : ℕ) [Fact p.Prime]
    (hM : 0 < M) (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1)
    (u : SmoothUpperSeed) (v : AutomorphicSpace (p * M)) :
    inner ℂ (poincareSeedVector (p * M) u) (HeckeL2.normalizer M p hM A B hAB v) =
      inner ℂ (poincareSeedVector (p * M)
        (primeNormalizerSeed M p (Fact.out : p.Prime).pos A B hAB u)) v := by
  have he : (fun v : AutomorphicSpace (p * M) =>
      inner ℂ (poincareSeedVector (p * M) u) (HeckeL2.normalizer M p hM A B hAB v)) =
      fun v => inner ℂ (poincareSeedVector (p * M)
        (primeNormalizerSeed M p (Fact.out : p.Prime).pos A B hAB u)) v := by
    apply (AutomorphicL2.denseEmbedding_dense (gamma (p * M))
      (quotientMeasure (p * M))).equalizer
      (continuous_const.inner (HeckeL2.normalizer M p hM A B hAB).continuous)
      (continuous_const.inner continuous_id)
    funext f
    simp only [Function.comp_apply, id_eq, primeNormalizer_apply, poincareSeed_pairing_representative]
    exact primeNormalizer_seed_pairing M p (Fact.out : p.Prime).pos A B hAB u f.val
  exact congrFun he v

/-- Local Atkin--Lehner preserves the full physical Friedrichs graph,
proved by transformed compact tests and the existing graph criterion. -/
theorem primeNormalizer_friedrichsGraph (M p : ℕ) [Fact p.Prime]
    (hM : 0 < M) (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1)
    {v w : AutomorphicSpace (p * M)} (h : FriedrichsGraph (p * M) v w) :
    FriedrichsGraph (p * M) (HeckeL2.normalizer M p hM A B hAB v)
      (HeckeL2.normalizer M p hM A B hAB w) := by
  let : NeZero M := ⟨hM.ne'⟩
  apply friedrichsGraph_of_seed_pairings
  intro u
  rw [poincareSeed_pairing_primeNormalizer, poincareSeed_pairing_primeNormalizer]
  have hs := friedrichsGraph_poincareSeed (p * M)
    (primeNormalizerSeed M p (Fact.out : p.Prime).pos A B hAB u)
  rw [primeNormalizerSeed_laplacian] at hs
  exact friedrichsGraph_symmetric (p * M) hs h

theorem primeNormalizer_resolvent (M p : ℕ) [Fact p.Prime]
    (hM : 0 < M) (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1)
    (v : AutomorphicSpace (p * M)) :
    friedrichsResolvent (p * M) (HeckeL2.normalizer M p hM A B hAB v) =
      HeckeL2.normalizer M p hM A B hAB (friedrichsResolvent (p * M) v) := by
  have h := primeNormalizer_friedrichsGraph M p hM A B hAB (friedrichsGraph_resolvent (p * M) v)
  simpa [FriedrichsGraph] using h

/-- Integral positive matrices admit the same cusp reduction used for
global Fricke. This general form also applies to every local normalizer. -/
theorem integralMatrix_cusp_triangular (G : Matrix (Fin 2) (Fin 2) ℤ)
    (hG : 0 < G.det) (g : GL (Fin 2) ℝ) (hg : g.val = G.map (Int.castRingHom ℝ))
    (s : SL(2, ℤ)) :
    ∃ (U : SL(2, ℤ)) (a b d : ℤ) (ha : 0 < a) (hd : 0 < d),
      g * SpecialLinearGroup.mapGL ℝ s = SpecialLinearGroup.mapGL ℝ U *
        triangularGL (a : ℝ) (b : ℝ) (d : ℝ)
          (by exact_mod_cast ha) (by exact_mod_cast hd) := by
  obtain ⟨U, a, b, d, ha, hd, he⟩ := integral_triangular (G * s.val)
    (by rw [Matrix.det_mul, s.property, mul_one]; exact hG)
  refine ⟨U, a, b, d, ha, hd, ?_⟩
  apply Units.ext
  change g.val * s.val.map (Int.castRingHom ℝ) =
    U.val.map (Int.castRingHom ℝ) * !![(a : ℝ), (b : ℝ); 0, (d : ℝ)]
  rw [hg]
  ext i j
  have hh := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℤ => (X i j : ℝ)) he
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add, Int.cast_mul] at hh
  fin_cases i <;> fin_cases j <;>
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using hh

theorem heckeNormalizerReal_integral (M p : ℕ) (hp : 0 < p)
    (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1) :
    (heckeNormalizerReal M p hp A B hAB).val =
      (!![(p : ℤ) * A, -B; (p : ℤ) * M, p] : Matrix (Fin 2) (Fin 2) ℤ).map
        (Int.castRingHom ℝ) := by
  change (SpecialLinearGroup.mapGL ℝ (heckeSL M p A B hAB)⁻¹).val *
    (dilationReal p hp).val = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.SL2_inv_expl, heckeSL, dilationReal, dilationGL,
      GeneralLinearGroup.map, GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

theorem cuspProfile_matrix_coordinates (N : ℕ) (hN : 0 < N) (g : GL (Fin 2) ℝ)
    (s U : SL(2, ℤ)) (a b d : ℤ) (ha : 0 < a) (hd : 0 < d)
    (he : g * SpecialLinearGroup.mapGL ℝ s = SpecialLinearGroup.mapGL ℝ U *
      triangularGL (a : ℝ) (b : ℝ) (d : ℝ)
        (by exact_mod_cast ha) (by exact_mod_cast hd))
    (f : ℍ → ℂ) (x y : ℝ) (hy : 0 < y) :
    cuspProfile N s (fun z => f (g • z)) x y =
      cuspProfile N U f ((a : ℝ) / d * x + (b : ℝ) / d / N) ((a : ℝ) / d * y) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hNy : (0 : ℝ) < (a : ℝ) / d * y := mul_pos (div_pos haR hdR) hy
  simp only [cuspProfile, dite_eq_left hy, dite_eq_left hNy]
  rw [← mul_smul, he, mul_smul, triangularGL_action]
  congr 1
  congr 1
  apply UpperHalfPlane.ext
  apply Complex.ext
  · simp only [affine, horocyclePoint, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
  · simp only [affine, horocyclePoint, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]

/-- Cusp constants are transported by a proved rational affine coordinate
change and by the actual automorphy of the normalizer representative. -/
theorem primeNormalizerRepresentative_constant_zero (M p : ℕ) [Fact p.Prime]
    (hM : 0 < M) (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1)
    (f : AutomorphicL2.representatives (gamma (p * M)) (quotientMeasure (p * M)))
    (hf : Continuous f.val)
    (hzero : ∀ s : SL(2, ℤ), ∀ y : ℝ, 0 < y → cuspConstant (p * M) s f.val y = 0)
    (s : SL(2, ℤ)) (y : ℝ) (hy : 0 < y) :
    cuspConstant (p * M) s (primeNormalizerRepresentative M p hM A B hAB f).val y = 0 := by
  have hp : p.Prime := Fact.out
  let G : Matrix (Fin 2) (Fin 2) ℤ := !![(p : ℤ) * A, -B; (p : ℤ) * M, p]
  have hG : 0 < G.det := by
    have he : G.det = (p : ℤ) := by
      rw [Matrix.det_fin_two]
      change ((p : ℤ) * A) * p - (-B) * ((p : ℤ) * M) = p
      linear_combination (p : ℤ) * hAB
    rw [he]
    exact_mod_cast hp.pos
  obtain ⟨U, a, b, d, ha, hd, he⟩ := integralMatrix_cusp_triangular G hG
    (heckeNormalizerReal M p hp.pos A B hAB) (heckeNormalizerReal_integral M p hp.pos A B hAB) s
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hval : (primeNormalizerRepresentative M p hM A B hAB f).val =
      fun z => f.val (heckeNormalizerReal M p hp.pos A B hAB • z) := by
    funext z
    exact congrArg f.val (heckeNormalizer_action M p hp.pos A B hAB z).symm
  have hcoord : (fun x => cuspProfile (p * M) s
      (primeNormalizerRepresentative M p hM A B hAB f).val x y) =
      fun x => cuspProfile (p * M) U f.val
        ((a : ℝ) / d * x + (b : ℝ) / d / (p * M)) ((a : ℝ) / d * y) := by
    rw [hval]
    funext x
    simpa only [Nat.cast_mul] using cuspProfile_matrix_coordinates (p * M) (Nat.mul_pos hp.pos hM) _
      s U a b d ha hd he f.val x y hy
  have hperiod := cuspProfile_periodic (p * M) s
    (primeNormalizerRepresentative M p hM A B hAB f).val
    (primeNormalizerRepresentative M p hM A B hAB f).property.2.1 y
  rw [hcoord] at hperiod
  unfold cuspConstant zeroFourier
  rw [hcoord, periodic_mean_rational_affine _
    (cuspProfile_continuous (p * M) U f.val hf ((a : ℝ) / d * y))
    (cuspProfile_periodic (p * M) U f.val f.property.2.1 ((a : ℝ) / d * y))
    a d ha.ne' hd.ne' ((b : ℝ) / d / (p * M)) hperiod]
  exact hzero U ((a : ℝ) / d * y) (mul_pos (div_pos haR hdR) hy)

theorem primeNormalizer_mem_cuspidal_continuous (M p : ℕ) [Fact p.Prime]
    (hM : 0 < M) (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1)
    (f : AutomorphicL2.representatives (gamma (p * M)) (quotientMeasure (p * M)))
    (hf : Continuous f.val)
    (hv : AutomorphicL2.denseEmbedding _ _ f ∈
      localCuspidalSpace (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM)) :
    HeckeL2.normalizer M p hM A B hAB (AutomorphicL2.denseEmbedding _ _ f) ∈
      localCuspidalSpace (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM) := by
  rw [primeNormalizer_apply]
  apply continuous_representative_mem_cuspidal (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM)
    _ (primeNormalizerRepresentative_continuous M p hM A B hAB f hf)
  apply primeNormalizerRepresentative_constant_zero M p hM A B hAB f hf
  exact localCuspidalSpace_continuous_constant_zero (p * M)
    (Nat.mul_pos (Fact.out : p.Prime).pos hM) (AutomorphicL2.denseEmbedding _ _ f) hv
    f.val hf f.property.2.1 f.property.2.2.coeFn_toLp

theorem primeNormalizer_mem_cuspidal (M p : ℕ) [Fact p.Prime]
    (hM : 0 < M) (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1)
    (v : AutomorphicSpace (p * M))
    (hv : v ∈ localCuspidalSpace (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM)) :
    HeckeL2.normalizer M p hM A B hAB v ∈
      localCuspidalSpace (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM) :=
  cuspidal_operator_mem_of_continuous (p * M) (p * M)
    (Nat.mul_pos (Fact.out : p.Prime).pos hM) (Nat.mul_pos (Fact.out : p.Prime).pos hM)
    (HeckeL2.normalizer M p hM A B hAB).toContinuousLinearMap
    (primeNormalizer_mem_cuspidal_continuous M p hM A B hAB) v hv

def primeNormalizerReflectionSL (M p : ℕ) (A B : ℤ)
    (hAB : (p : ℤ) * A + (M : ℤ) * B = 1) : SL(2, ℤ) :=
  ⟨!![(p : ℤ) * A - M * B, -2 * A * B;
      2 * p * M, (p : ℤ) * A - M * B], by
    rw [Matrix.det_fin_two]
    change ((p : ℤ) * A - M * B) * ((p : ℤ) * A - M * B) -
      (-2 * A * B) * (2 * p * M) = 1
    calc
      _ = ((p : ℤ) * A + M * B) ^ 2 := by ring
      _ = 1 := by rw [hAB]; norm_num⟩

theorem primeNormalizerReflectionSL_mem (M p : ℕ) (A B : ℤ)
    (hAB : (p : ℤ) * A + (M : ℤ) * B = 1) :
    primeNormalizerReflectionSL M p A B hAB ∈ CongruenceSubgroup.Gamma0 (p * M) := by
  rw [gamma0_mem_dvd]
  refine ⟨2, ?_⟩
  change (2 : ℤ) * p * M = ((p * M : ℕ) : ℤ) * 2
  rw [Nat.cast_mul]
  ring

/-- The reflection commutator is an explicit matrix in Gamma0(p*M). -/
theorem primeNormalizerReal_reflection (M p : ℕ) (hp : 0 < p)
    (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1) :
    heckeNormalizerReal M p hp A B hAB * J =
      SpecialLinearGroup.mapGL ℝ (primeNormalizerReflectionSL M p A B hAB) * J *
        heckeNormalizerReal M p hp A B hAB := by
  have hab : (p : ℝ) * A + (M : ℝ) * B = 1 := by exact_mod_cast hAB
  apply Units.ext
  change (heckeNormalizerReal M p hp A B hAB).val * J.val =
    (primeNormalizerReflectionSL M p A B hAB).val.map (Int.castRingHom ℝ) * J.val *
      (heckeNormalizerReal M p hp A B hAB).val
  rw [heckeNormalizerReal_integral]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [primeNormalizerReflectionSL, J, GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply, Fin.sum_univ_two]
  all_goals first
    | linear_combination (p : ℝ) * A * hab
    | linear_combination (B : ℝ) * hab
    | linear_combination (p : ℝ) * M * hab
    | linear_combination -(p : ℝ) * hab

theorem primeNormalizer_function_reflection (M p : ℕ) [Fact p.Prime]
    (_hM : 0 < M) (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1)
    (f : AutomorphicL2.representatives (gamma (p * M)) (quotientMeasure (p * M))) (z : ℍ) :
    f.val (heckeNormalizerLabel M p (Fact.out : p.Prime).pos A B hAB • (J • z)) =
      f.val (J • (heckeNormalizerLabel M p (Fact.out : p.Prime).pos A B hAB • z)) := by
  rw [← heckeNormalizer_action, ← heckeNormalizer_action, ← mul_smul,
    primeNormalizerReal_reflection, mul_smul, mul_smul]
  exact representative_matrix_invariant (p * M) f
    ⟨SpecialLinearGroup.mapGL ℝ (primeNormalizerReflectionSL M p A B hAB),
      ⟨_, primeNormalizerReflectionSL_mem M p A B hAB, rfl⟩⟩ _

theorem primeNormalizer_reflection (M p : ℕ) [Fact p.Prime]
    (hM : 0 < M) (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1)
    (v : AutomorphicSpace (p * M)) :
    HeckeL2.normalizer M p hM A B hAB (reflectionIsometry (p * M) v) =
      reflectionIsometry (p * M) (HeckeL2.normalizer M p hM A B hAB v) := by
  have he : (fun v : AutomorphicSpace (p * M) =>
      HeckeL2.normalizer M p hM A B hAB (reflectionIsometry (p * M) v)) =
      fun v => reflectionIsometry (p * M) (HeckeL2.normalizer M p hM A B hAB v) := by
    apply (AutomorphicL2.denseEmbedding_dense (gamma (p * M))
      (quotientMeasure (p * M))).equalizer
      ((HeckeL2.normalizer M p hM A B hAB).continuous.comp (reflectionIsometry (p * M)).continuous)
      ((reflectionIsometry (p * M)).continuous.comp (HeckeL2.normalizer M p hM A B hAB).continuous)
    funext f
    simp only [Function.comp_apply, primeNormalizer_apply, reflectionIsometry_apply]
    apply congrArg (AutomorphicL2.denseEmbedding _ _)
    apply Subtype.ext
    funext z
    exact (primeNormalizer_function_reflection M p hM A B hAB f z).symm
  exact congrFun he v

#print axioms primeNormalizer_apply
#print axioms primeNormalizerRepresentative_continuous
#print axioms primeNormalizer_involutive
#print axioms inverse_affine_dilation
#print axioms primeNormalizerSeed_cancel
#print axioms primeNormalizerSeed_laplacian
#print axioms primeNormalizer_seed_pairing
#print axioms poincareSeed_pairing_primeNormalizer
#print axioms primeNormalizer_friedrichsGraph
#print axioms primeNormalizer_resolvent
#print axioms integralMatrix_cusp_triangular
#print axioms heckeNormalizerReal_integral
#print axioms cuspProfile_matrix_coordinates
#print axioms primeNormalizerRepresentative_constant_zero
#print axioms primeNormalizer_mem_cuspidal_continuous
#print axioms primeNormalizer_mem_cuspidal
#print axioms primeNormalizerReflectionSL_mem
#print axioms primeNormalizerReal_reflection
#print axioms primeNormalizer_function_reflection
#print axioms primeNormalizer_reflection

end QuantitativeNinaMaass
