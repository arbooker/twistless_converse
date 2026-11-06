module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Isometric
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public section

/-!
Actual spectral cut subspaces on arbitrary complex Hilbert spaces. A low cut
is the kernel of the positive part of `A-a I`, constructed by continuous
functional calculus. Thus this construction does not assume a Borel spectral
calculus, a finite-dimensional diagonalization, or a spectral-measure axiom.
The cut contains the threshold eigenspace; its orthogonal complement is the
strict high cut. The weak quadratic inequalities hold on both closed spaces.
-/

namespace QuantitativeSpectralCut

open ContinuousLinearMap InnerProductSpace
open scoped InnerProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Fix the inherited real scalar structure before specializing to orbit spaces. -/
noncomputable def positivePart (A : H →L[ℂ] H) : H →L[ℂ] H := A⁺

theorem positivePart_eq_cfc (A : H →L[ℂ] H) :
    positivePart A = cfc (fun r : ℝ => r⁺) A := by
  unfold positivePart
  rw [CFC.posPart_def, cfcₙ_eq_cfc]

theorem positivePart_norm_le (A : H →L[ℂ] H) : ‖positivePart A‖ ≤ ‖A‖ :=
  CStarAlgebra.norm_posPart_le A

noncomputable def low (A : H →L[ℂ] H) : Submodule ℂ H := A⁺.ker

noncomputable def high (A : H →L[ℂ] H) : Submodule ℂ H := (low A)ᗮ

instance high_complete (A : H →L[ℂ] H) : CompleteSpace (high A) :=
  (low A).isClosed_orthogonal.completeSpace_coe

instance low_complete (A : H →L[ℂ] H) : CompleteSpace (low A) :=
  A⁺.isClosed_ker.completeSpace_coe

/-- The negative part vanishes on the strict high cut. -/
theorem negativePart_eq_zero_of_high (A : H →L[ℂ] H) {v : H} (hv : v ∈ high A) :
    A⁻ v = 0 := by
  have hp : A⁻.IsPositive := nonneg_iff_isPositive.mp (CFC.negPart_nonneg A)
  apply ext_inner_right ℂ
  intro w
  rw [inner_zero_left, hp.inner_left_eq_inner_right]
  apply ((low A).mem_orthogonal' v).mp hv
  change A⁺ (A⁻ w) = 0
  have h := congrArg (fun B : H →L[ℂ] H => B w) (CFC.posPart_mul_negPart A)
  exact h

/-- On the low cut a self-adjoint operator has nonpositive quadratic form. -/
theorem quadratic_nonpos_on_low (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    {v : H} (hv : v ∈ low A) : (⟪A v, v⟫_ℂ).re ≤ 0 := by
  have hv' : A⁺ v = 0 := hv
  have he := congrArg (fun B : H →L[ℂ] H => B v) (CFC.posPart_sub_negPart A hA)
  simp only [sub_apply, hv', zero_sub] at he
  rw [← he, inner_neg_left, Complex.neg_re]
  exact neg_nonpos.mpr ((nonneg_iff_isPositive.mp (CFC.negPart_nonneg A)).re_inner_nonneg_left v)

/-- On the high cut a self-adjoint operator has nonnegative quadratic form. -/
theorem quadratic_nonneg_on_high (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    {v : H} (hv : v ∈ high A) : 0 ≤ (⟪A v, v⟫_ℂ).re := by
  have he := congrArg (fun B : H →L[ℂ] H => B v) (CFC.posPart_sub_negPart A hA)
  simp only [sub_apply, negativePart_eq_zero_of_high A hv, sub_zero] at he
  rw [← he]
  exact (nonneg_iff_isPositive.mp (CFC.posPart_nonneg A)).re_inner_nonneg_left v

/-- The low cut is invariant under its self-adjoint operator. -/
theorem maps_low (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    {v : H} (hv : v ∈ low A) : A v ∈ low A := by
  change A⁺ (A v) = 0
  have he := congrArg (fun B : H →L[ℂ] H => B v) (CFC.posPart_sub_negPart A hA)
  have hv' : A⁺ v = 0 := hv
  simp only [sub_apply, hv', zero_sub] at he
  rw [← he, map_neg]
  have hz := congrArg (fun B : H →L[ℂ] H => B v) (CFC.posPart_mul_negPart A)
  change A⁺ (A⁻ v) = 0 at hz
  rw [hz, neg_zero]

/-- The two cut spaces have orthogonal images under any self-adjoint
operator commuting with the defining operator; here is the intrinsic case.
This is the off-diagonal vanishing needed in triangular spectral deflation. -/
theorem cut_off_diagonal (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    {v w : H} (hv : v ∈ high A) (hw : w ∈ low A) : ⟪v, A w⟫_ℂ = 0 :=
  ((low A).mem_orthogonal' v).mp hv _ (maps_low A hA hw)

/-- Every nonpositive eigenvector is in the low cut. In particular,
zero modes are retained exactly, without approximating the cut projection. -/
theorem nonpos_eigen_mem_low (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    {c : ℝ} (hc : c ≤ 0) {v : H} (hv : A v = c • v) : v ∈ low A := by
  have hp : A⁺.IsPositive := nonneg_iff_isPositive.mp (CFC.posPart_nonneg A)
  have hz : A⁺ (A⁻ v) = 0 :=
    congrArg (fun B : H →L[ℂ] H => B v) (CFC.posPart_mul_negPart A)
  have ho : ⟪A⁺ v, A⁻ v⟫_ℂ = 0 := by
    rw [hp.inner_left_eq_inner_right, hz, inner_zero_right]
  have he := congrArg (fun B : H →L[ℂ] H => B v) (CFC.posPart_sub_negPart A hA)
  change A⁺ v - A⁻ v = A v at he
  have hi : (⟪A⁺ v, A v⟫_ℂ).re = ‖A⁺ v‖^2 := by
    rw [← he, inner_sub_right, ho, sub_zero, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  have hn := mul_nonpos_of_nonpos_of_nonneg hc (hp.re_inner_nonneg_left v)
  have hi' : (⟪A⁺ v, A v⟫_ℂ).re = c * (⟪A⁺ v, v⟫_ℂ).re := by
    rw [hv, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_real_right]
    simp
  change c * (⟪A⁺ v, v⟫_ℂ).re ≤ 0 at hn
  have hnorm : ‖A⁺ v‖ = 0 := by nlinarith [norm_nonneg (A⁺ v)]
  exact norm_eq_zero.mp hnorm

/-- Shifted cuts at a prescribed real threshold. -/
noncomputable def lowAt (A : H →L[ℂ] H) (a : ℝ) : Submodule ℂ H :=
  low (A - a • (1 : H →L[ℂ] H))

noncomputable def highAt (A : H →L[ℂ] H) (a : ℝ) : Submodule ℂ H :=
  high (A - a • (1 : H →L[ℂ] H))

instance lowAt_complete (A : H →L[ℂ] H) (a : ℝ) : CompleteSpace (lowAt A a) :=
  low_complete (A - a • (1 : H →L[ℂ] H))

instance highAt_complete (A : H →L[ℂ] H) (a : ℝ) : CompleteSpace (highAt A a) :=
  (lowAt A a).isClosed_orthogonal.completeSpace_coe

theorem shifted_selfAdjoint (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (a : ℝ) :
    IsSelfAdjoint (A - a • (1 : H →L[ℂ] H)) :=
  hA.sub ((IsSelfAdjoint.all a).smul (IsSelfAdjoint.one _))

omit [CompleteSpace H] in
private theorem shifted_quadratic (A : H →L[ℂ] H) (a : ℝ) (v : H) :
    (⟪(A - a • (1 : H →L[ℂ] H)) v, v⟫_ℂ).re =
      (⟪A v, v⟫_ℂ).re - a * ‖v‖^2 := by
  change (⟪A v - a • v, v⟫_ℂ).re = _
  rw [inner_sub_left, Complex.sub_re, RCLike.real_smul_eq_coe_smul (K := ℂ),
    inner_smul_real_left, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

/-- The actual low spectral cut satisfies the threshold quadratic bound. -/
theorem quadratic_le_on_lowAt (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (a : ℝ)
    {v : H} (hv : v ∈ lowAt A a) : (⟪A v, v⟫_ℂ).re ≤ a * ‖v‖^2 := by
  have h := quadratic_nonpos_on_low _ (shifted_selfAdjoint A hA a) hv
  rw [shifted_quadratic] at h
  linarith

/-- The actual high spectral cut satisfies the threshold quadratic bound. -/
theorem quadratic_ge_on_highAt (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (a : ℝ)
    {v : H} (hv : v ∈ highAt A a) : a * ‖v‖^2 ≤ (⟪A v, v⟫_ℂ).re := by
  have h := quadratic_nonneg_on_high _ (shifted_selfAdjoint A hA a) hv
  rw [shifted_quadratic] at h
  linarith

/-- Opposite threshold spaces are orthogonal after applying `A`. -/
theorem threshold_off_diagonal (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (a : ℝ)
    {v w : H} (hv : v ∈ highAt A a) (hw : w ∈ lowAt A a) : ⟪v, A w⟫_ℂ = 0 := by
  have h := cut_off_diagonal _ (shifted_selfAdjoint A hA a) hv hw
  have hz : ⟪v, w⟫_ℂ = 0 :=
    ((low (A - a • (1 : H →L[ℂ] H))).mem_orthogonal' v).mp hv w hw
  change ⟪v, A w - a • w⟫_ℂ = 0 at h
  rw [inner_sub_right, RCLike.real_smul_eq_coe_smul (K := ℂ),
    inner_smul_real_right, hz, smul_zero, sub_zero] at h
  exact h

/-- Quadratic majorization by the low threshold and the high cut. This is
the operator estimate underlying extraction of high-cut trace mass. -/
theorem quadratic_cut_majorant (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    {a M : ℝ} (ha : 0 ≤ a) (hM : ‖A‖ ≤ M) (x : H) :
    (⟪A x, x⟫_ℂ).re ≤ a * ‖x‖^2 +
      M * ‖x - (lowAt A a).starProjection x‖^2 := by
  let U := lowAt A a
  let u := U.starProjection x
  let v := x-u
  have hu : u ∈ U := U.starProjection_apply_mem x
  have hv : v ∈ highAt A a := U.sub_starProjection_mem_orthogonal x
  have hcross : ⟪v, A u⟫_ℂ = 0 := threshold_off_diagonal A hA a hv hu
  have hcross' : ⟪A u, v⟫_ℂ = 0 := inner_eq_zero_symm.mp hcross
  have hsym := isSelfAdjoint_iff_isSymmetric.mp hA
  have hcross'' : ⟪A v, u⟫_ℂ = 0 := (hsym v u).trans hcross
  have henergy : (⟪A x, x⟫_ℂ).re = (⟪A u, u⟫_ℂ).re + (⟪A v, v⟫_ℂ).re := by
    have hx : x = u+v := by dsimp [v]; abel
    conv_lhs => rw [hx]
    simp only [map_add, inner_add_left, inner_add_right, hcross', hcross'',
      add_zero, zero_add, Complex.add_re]
  have hlu := quadratic_le_on_lowAt A hA a hu
  have hhv := re_inner_le_norm (𝕜 := ℂ) (A v) v
  change (⟪A v, v⟫_ℂ).re ≤ ‖A v‖ * ‖v‖ at hhv
  have hnorm := (A.le_opNorm v).trans (mul_le_mul_of_nonneg_right hM (norm_nonneg v))
  have hhv' : (⟪A v, v⟫_ℂ).re ≤ M * ‖v‖^2 := by
    nlinarith [mul_le_mul_of_nonneg_right hnorm (norm_nonneg v)]
  have hunorm : ‖u‖ ≤ ‖x‖ := U.norm_starProjection_apply_le x
  have hsq : ‖u‖^2 ≤ ‖x‖^2 := pow_le_pow_left₀ (norm_nonneg u) hunorm 2
  have hlow := mul_le_mul_of_nonneg_left hsq ha
  change (⟪A x, x⟫_ℂ).re ≤ a * ‖x‖^2 + M * ‖v‖^2
  linarith

/-- Known residual kernel vectors survive a nonnegative spectral cut. -/
theorem kernel_mem_lowAt (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    {a : ℝ} (ha : 0 ≤ a) {v : H} (hv : A v = 0) : v ∈ lowAt A a := by
  apply nonpos_eigen_mem_low _ (shifted_selfAdjoint A hA a) (neg_nonpos.mpr ha)
  change A v - a • v = -a • v
  rw [hv, zero_sub, neg_smul]

/-- A nonnegative high cut of an operator supported in a closed corner
is contained in that corner. -/
theorem highAt_le_corner (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (P : Submodule ℂ H) [CompleteSpace P] {a : ℝ} (ha : 0 ≤ a)
    (hAP : A.comp P.starProjection = A) : highAt A a ≤ P := by
  have hker : Pᗮ ≤ lowAt A a := by
    intro w hw
    apply kernel_mem_lowAt A hA ha
    have hp : P.starProjection w = 0 := by
      rw [Submodule.starProjection_apply,
        P.orthogonalProjectionOnto_apply_of_mem_orthogonal hw, Submodule.coe_zero]
    have h := congrArg (fun B : H →L[ℂ] H => B w) hAP
    simpa only [comp_apply, hp, map_zero] using h.symm
  have hh := Submodule.orthogonal_le hker
  simpa only [highAt, high, lowAt, Submodule.orthogonal_orthogonal] using hh

/-- The majorant on a finite corner charges only its projection, rather
than the infinite-dimensional identity of the ambient Hilbert space. -/
theorem corner_quadratic_majorant (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (P : Submodule ℂ H) [CompleteSpace P] {a M : ℝ} (ha : 0 ≤ a)
    (hM : ‖A‖ ≤ M) (hAP : A.comp P.starProjection = A) (x : H) :
    (⟪A x, x⟫_ℂ).re ≤ a * ‖P.starProjection x‖^2 +
      M * ‖(highAt A a).starProjection x‖^2 := by
  have hp := highAt_le_corner A hA P ha hAP
  have hproj : (highAt A a).starProjection (P.starProjection x) =
      (highAt A a).starProjection x := by
    simp only [Submodule.starProjection_apply]
    congr 1
    exact Submodule.orthogonalProjectionOnto_starProjection_of_le hp x
  have hdiag : ⟪A (P.starProjection x), P.starProjection x⟫_ℂ = ⟪A x, x⟫_ℂ := by
    have hAX : A (P.starProjection x) = A x := congrArg (fun B : H →L[ℂ] H => B x) hAP
    have hAP' := congrArg ContinuousLinearMap.adjoint hAP
    have hself := isSelfAdjoint_iff'.mp hA
    have hpself : P.starProjection.adjoint = P.starProjection := isSelfAdjoint_starProjection P
    simp only [adjoint_comp, hself, hpself] at hAP'
    have hPX : P.starProjection (A x) = A x := congrArg (fun B : H →L[ℂ] H => B x) hAP'
    rw [hAX]
    calc
      ⟪A x, P.starProjection x⟫_ℂ = ⟪P.starProjection (A x), x⟫_ℂ :=
        (P.starProjection_isSymmetric (A x) x).symm
      _ = ⟪A x, x⟫_ℂ := by rw [hPX]
  have h := quadratic_cut_majorant A hA ha hM (P.starProjection x)
  rw [hdiag] at h
  have hhigh : (highAt A a).starProjection (P.starProjection x) =
      P.starProjection x - (lowAt A a).starProjection (P.starProjection x) :=
    (lowAt A a).starProjection_orthogonal_val _
  rw [← hhigh, hproj] at h
  exact h

/-- Projection onto the high cut is injective on every subspace with a
strictly larger quadratic lower bound. This is the geometric min--max step. -/
theorem high_projection_injective_on (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (U : Submodule ℂ H) {a b : ℝ} (hab : a < b)
    (hcoercive : ∀ v ∈ U, b * ‖v‖^2 ≤ (⟪A v, v⟫_ℂ).re)
    {v : H} (hv : v ∈ U) (hz : (highAt A a).starProjection v = 0) : v = 0 := by
  have hmem : v ∈ (highAt A a)ᗮ := by
    rw [← Submodule.ker_starProjection]
    exact hz
  have hlow : v ∈ lowAt A a := by
    simpa only [highAt, high, lowAt, Submodule.orthogonal_orthogonal] using hmem
  have hu := quadratic_le_on_lowAt A hA a hlow
  have hl := hcoercive v hv
  have hsq : ‖v‖^2 ≤ 0 := le_of_not_gt (fun hh =>
    (not_lt_of_ge (hl.trans hu)) (mul_lt_mul_of_pos_right hab hh))
  have hn : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
  exact norm_eq_zero.mp hn

/-- The map from a coercive corner to the high spectral cut has precisely
the orthogonal complement of that corner as its kernel. -/
theorem high_restriction_kernel (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (U : Submodule ℂ H) [CompleteSpace U] {a b : ℝ} (hab : a < b)
    (hcoercive : ∀ v ∈ U, b * ‖v‖^2 ≤ (⟪A v, v⟫_ℂ).re) :
    ((highAt A a).starProjection.comp U.starProjection).ker = Uᗮ := by
  rw [← Submodule.ker_starProjection]
  ext v
  change (highAt A a).starProjection (U.starProjection v) = 0 ↔ U.starProjection v = 0
  constructor
  · exact fun hz => high_projection_injective_on A hA U hab hcoercive
      (U.starProjection_apply_mem v) hz
  · intro hz
    rw [hz, map_zero]

/-- Opposite cut spaces have orthogonal images under a residual operator.
This is the exact zero block used to make the deflation operator triangular,
rather than a bound obtained by adding one error for every prime. -/
theorem residual_images_orthogonal {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] (B : H →L[ℂ] J) (a : ℝ)
    {v w : H} (hv : v ∈ highAt (B.adjoint.comp B) a)
    (hw : w ∈ lowAt (B.adjoint.comp B) a) : ⟪B v, B w⟫_ℂ = 0 := by
  have hA : IsSelfAdjoint (B.adjoint.comp B) := by
    rw [isSelfAdjoint_iff']
    simp only [adjoint_comp, adjoint_adjoint]
  have h := cut_off_diagonal _ (shifted_selfAdjoint _ hA a) hv hw
  have hz : ⟪v, w⟫_ℂ = 0 :=
    ((low (B.adjoint.comp B - a • (1 : H →L[ℂ] H))).mem_orthogonal' v).mp hv w hw
  change ⟪v, B.adjoint (B w) - a • w⟫_ℂ = 0 at h
  rw [inner_sub_right, RCLike.real_smul_eq_coe_smul (K := ℂ),
    inner_smul_real_right, hz, smul_zero, sub_zero, adjoint_inner_right] at h
  exact h

#print axioms negativePart_eq_zero_of_high
#print axioms quadratic_nonpos_on_low
#print axioms quadratic_nonneg_on_high
#print axioms nonpos_eigen_mem_low
#print axioms kernel_mem_lowAt
#print axioms maps_low
#print axioms cut_off_diagonal
#print axioms quadratic_le_on_lowAt
#print axioms quadratic_ge_on_highAt
#print axioms threshold_off_diagonal
#print axioms quadratic_cut_majorant
#print axioms highAt_le_corner
#print axioms corner_quadratic_majorant
#print axioms high_projection_injective_on
#print axioms high_restriction_kernel
#print axioms residual_images_orthogonal

end QuantitativeSpectralCut
