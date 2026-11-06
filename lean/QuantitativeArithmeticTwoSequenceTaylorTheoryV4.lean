module

public import QuantitativeArithmeticTwoSequenceMellinRowsV1
public import QuantitativeArithmeticTwoSequenceStripRowsV1
public import SmallLevelTaylorRowNormalizationV1

/-! Consolidated chapter: QuantitativeArithmeticTwoSequenceTaylor. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticMatrixTwoSequenceV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticTwoSequenceTaylor
open SmallLevelTaylor SmallLevelAdditive Complex Filter Set MeasureTheory FinitenessFourierConstruction FinitenessPolynomialSeries
open scoped Topology

/-- A matrix transformation becomes a two-sequence Fricke relation after
translations by its two rational cusp coordinates. The scalar includes
whatever determinant normalization occurs in the given transformation. -/
theorem matrix_two_series (a : ℕ → ℂ) (k : ℕ) (A B C D : ℝ)
    (hC : C≠0) (hdet : 0<A*D-B*C) (χ : ℂ)
    (hF : ∀ z : ℂ, 0<z.im → fourier a z=
      χ/(((C:ℂ)*z+(D:ℂ))^k)*fourier a (((A:ℂ)*z+(B:ℂ))/((C:ℂ)*z+(D:ℂ)))) :
    let L := C^2/(A*D-B*C)
    let a₀ := coefficients a (-D/C)
    let b₀ := coefficients a (A/C)
    ∀ z : ℂ, 0<z.im → fourier a₀ z=
      (χ*((Real.sqrt L:ℂ)/(C:ℂ))^k)/(((Real.sqrt L:ℂ)*z)^k)*
        fourier b₀ (-1/((L:ℂ)*z)) := by
  dsimp only
  intro z hz
  have hc : (C:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hC
  have hd : ((A*D-B*C:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr hdet.ne'
  have hL : 0<C^2/(A*D-B*C) := div_pos (sq_pos_of_ne_zero hC) hdet
  have hs : (Real.sqrt (C^2/(A*D-B*C)):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hL).ne'
  have hz0 : z≠0 := by intro he; subst z; simp at hz
  have him : 0<(z+((-D/C:ℝ):ℂ)).im := by simpa using hz
  rw [fourier_translate,fourier_translate,hF _ him]
  have hden : (C:ℂ)*(z+((-D/C:ℝ):ℂ))+(D:ℂ)=(C:ℂ)*z := by
    push_cast
    field_simp
    ring
  have hpoint : ((A:ℂ)*(z+((-D/C:ℝ):ℂ))+(B:ℂ))/
      ((C:ℂ)*(z+((-D/C:ℝ):ℂ))+(D:ℂ))=
      -1/(((C^2/(A*D-B*C):ℝ):ℂ)*z)+((A/C:ℝ):ℂ) := by
    rw [hden]
    push_cast
    push_cast at hd
    field_simp
    ring
  rw [hpoint,hden]
  congr 1
  generalize (Real.sqrt (C^2/(A*D-B*C)):ℂ)=t at hs ⊢
  rw [div_pow, mul_pow]
  field_simp [hc,hz0,hs]
  ring1

#print axioms matrix_two_series
end QuantitativeArithmeticTwoSequenceTaylor
end
end

/-! ## QuantitativeArithmeticMatrixTaylorBoundedRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticTwoSequenceTaylor
open SmallLevelTaylor SmallLevelAdditive Complex Filter Set MeasureTheory FinitenessFourierConstruction FinitenessPolynomialSeries
open scoped Topology

/-- An actual positive-determinant matrix transformation yields the full
all-order Taylor-Mellin rows on translated Fourier series. No meromorphic
continuation, pole cancellation, or extra Hecke relation is an input. -/
theorem matrix_taylor_bounded_rows {a : ℕ → ℂ} (ha : PolynomialBound a) (ha0 : a 0=0)
    (k : ℕ) (A B C D : ℝ) (hC : C≠0) (hdet : 0<A*D-B*C) (χ : ℂ)
    (hF : ∀ z : ℂ, 0<z.im → fourier a z=
      χ/(((C:ℂ)*z+(D:ℂ))^k)*fourier a (((A:ℂ)*z+(B:ℂ))/((C:ℂ)*z+(D:ℂ)))) :
    let L := C^2/(A*D-B*C)
    let a₀ := coefficients a (-D/C)
    let b₀ := coefficients a (A/C)
    let χ₀ := χ*((Real.sqrt L:ℂ)/(C:ℂ))^k
    ∀ r : ℝ, r≠0 → ∃ bound : ℝ, ∀ M : ℕ,
      AnalyticOnNhd ℂ (mellin (twoError k a₀ b₀ L r χ₀ M))
        {s : ℂ | bound-(M:ℝ)<s.re} ∧
      QuantitativeArithmeticMellinStrip.BoundedSubstrips (bound-(M:ℝ))
        (mellin (twoError k a₀ b₀ L r χ₀ M)) ∧
      ∀ s : ℂ, bound<s.re →
        transform a₀ r s-
          (χ₀/(((Real.sqrt L:ℂ)*(r:ℂ))^k))*
            (∑ n∈Finset.range M, mellinTaylorTerm k b₀ (-1/(L*r)) (L*r^2) r n s)=
          mellin (twoError k a₀ b₀ L r χ₀ M) s := by
  dsimp only
  intro r hr
  exact two_taylor_bounded_rows (div_pos (sq_pos_of_ne_zero hC) hdet) hr k
    (coefficients_polynomial ha (-D/C)) (coefficients_zero ha0 (-D/C))
    (coefficients_polynomial ha (A/C)) (coefficients_zero ha0 (A/C)) _
    (matrix_two_series a k A B C D hC hdet χ hF)

#print axioms matrix_taylor_bounded_rows
end QuantitativeArithmeticTwoSequenceTaylor
end
end

/-! ## QuantitativeArithmeticMatrixTaylorRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticTwoSequenceTaylor
open SmallLevelTaylor SmallLevelAdditive Complex Filter Set MeasureTheory FinitenessFourierConstruction FinitenessPolynomialSeries
open scoped Topology

/-- An actual positive-determinant matrix transformation yields the full
all-order Taylor-Mellin rows on translated Fourier series. No meromorphic
continuation, pole cancellation, or extra Hecke relation is an input. -/
theorem matrix_taylor_rows {a : ℕ → ℂ} (ha : PolynomialBound a) (ha0 : a 0=0)
    (k : ℕ) (A B C D : ℝ) (hC : C≠0) (hdet : 0<A*D-B*C) (χ : ℂ)
    (hF : ∀ z : ℂ, 0<z.im → fourier a z=
      χ/(((C:ℂ)*z+(D:ℂ))^k)*fourier a (((A:ℂ)*z+(B:ℂ))/((C:ℂ)*z+(D:ℂ)))) :
    let L := C^2/(A*D-B*C)
    let a₀ := coefficients a (-D/C)
    let b₀ := coefficients a (A/C)
    let χ₀ := χ*((Real.sqrt L:ℂ)/(C:ℂ))^k
    ∀ r : ℝ, r≠0 → ∃ bound : ℝ, ∀ M : ℕ,
      AnalyticOnNhd ℂ (mellin (twoError k a₀ b₀ L r χ₀ M))
        {s : ℂ | bound-(M:ℝ)<s.re} ∧
      ∀ s : ℂ, bound<s.re →
        transform a₀ r s-
          (χ₀/(((Real.sqrt L:ℂ)*(r:ℂ))^k))*
            (∑ n∈Finset.range M, mellinTaylorTerm k b₀ (-1/(L*r)) (L*r^2) r n s)=
          mellin (twoError k a₀ b₀ L r χ₀ M) s := by
  dsimp only
  intro r hr
  exact two_taylor_mellin_rows (div_pos (sq_pos_of_ne_zero hC) hdet) hr k
    (coefficients_polynomial ha (-D/C)) (coefficients_zero ha0 (-D/C))
    (coefficients_polynomial ha (A/C)) (coefficients_zero ha0 (A/C)) _
    (matrix_two_series a k A B C D hC hdet χ hF)

#print axioms matrix_taylor_rows
end QuantitativeArithmeticTwoSequenceTaylor
end
end

/-! ## QuantitativeArithmeticMatrixNormalizedRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticTwoSequenceTaylor
open SmallLevelTaylor SmallLevelAdditive Complex Set MeasureTheory
open FinitenessPolynomialSeries FinitenessFourierConstruction

theorem coefficients_translate (a : ℕ → ℂ) (u v : ℝ) :
    coefficients (coefficients a u) v = coefficients a (u+v) := by
  funext n
  unfold coefficients phase
  rw [mul_assoc,← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem transform_translate (a : ℕ → ℂ) (u v : ℝ) (s : ℂ) :
    transform (coefficients a u) v s=transform a (u+v) s := by
  simp only [transform,coefficients_translate]

theorem matrix_partner (A B C D j : ℝ) (hC : C≠0)
    (_hdet : A*D-B*C≠0) (hj : C*j+D≠0) :
    A/C + -1/((C^2/(A*D-B*C))*(j+D/C))=(A*j+B)/(C*j+D) := by
  have hr : j+D/C≠0 := by
    intro h
    apply hj
    calc C*j+D=C*(j+D/C) := by field_simp
         _=0 := by rw [h,mul_zero]
  field_simp
  ring

/-- Actual matrix Taylor rows written in the original additive coordinates.
The entire error retreats by one half-plane unit per retained Taylor term. -/
theorem matrix_normalized_rows {a : ℕ → ℂ} (ha : PolynomialBound a) (ha0 : a 0=0)
    (k : ℕ) (hk : Even k) (A B C D j : ℝ) (hC : C≠0)
    (hdet : 0<A*D-B*C) (hj : C*j+D≠0) (χ : ℂ)
    (hF : ∀ z : ℂ, 0<z.im → fourier a z=
      χ/(((C:ℂ)*z+(D:ℂ))^k)*fourier a (((A:ℂ)*z+(B:ℂ))/((C:ℂ)*z+(D:ℂ)))) :
    let L := C^2/(A*D-B*C)
    let r := j+D/C
    let χ₀ := χ*((Real.sqrt L:ℂ)/(C:ℂ))^k
    ∃ bound : ℝ, ∀ M : ℕ,
      AnalyticOnNhd ℂ (mellin (twoError k (coefficients a (-D/C))
        (coefficients a (A/C)) L r χ₀ M)) {s : ℂ | bound-(M:ℝ)<s.re} ∧
      ∀ s : ℂ, bound<s.re →
        transform a j s-χ₀*((L*r^2:ℝ):ℂ)^(s-((k:ℂ)/2))*
          (∑ n∈Finset.range M, (I*(L:ℂ)*(r:ℂ))^n*
            Ring.choose (s+(n:ℂ)-(k:ℂ)) n*
            transform a ((A*j+B)/(C*j+D)) (s+(n:ℂ))) =
          mellin (twoError k (coefficients a (-D/C)) (coefficients a (A/C)) L r χ₀ M) s := by
  dsimp only
  have hL : 0<C^2/(A*D-B*C) := div_pos (sq_pos_of_ne_zero hC) hdet
  have hr : j+D/C≠0 := by
    intro h
    apply hj
    calc C*j+D=C*(j+D/C) := by field_simp
         _=0 := by rw [h,mul_zero]
  obtain ⟨bound,hbound⟩ := matrix_taylor_rows ha ha0 k A B C D hC hdet χ hF (j+D/C) hr
  refine ⟨bound,fun M => ⟨(hbound M).1,?_⟩⟩
  intro s hs
  have he := (hbound M).2 s hs
  rw [normalized_taylor_sum hL hr k hk] at he
  simp only [normalizedTaylorSum,transform_translate] at he
  rw [show -D/C+(j+D/C)=j by ring,
    matrix_partner A B C D j hC hdet.ne' hj] at he
  exact he
#print axioms matrix_normalized_rows
end QuantitativeArithmeticTwoSequenceTaylor
end
end

/-! ## QuantitativeArithmeticMatrixNormalizedBoundedRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticTwoSequenceTaylor
open SmallLevelTaylor SmallLevelAdditive Complex Set MeasureTheory
open FinitenessPolynomialSeries FinitenessFourierConstruction
/-- Actual matrix Taylor rows written in the original additive coordinates.
The entire error retreats by one half-plane unit per retained Taylor term. -/
theorem matrix_normalized_bounded_rows {a : ℕ → ℂ} (ha : PolynomialBound a) (ha0 : a 0=0)
    (k : ℕ) (hk : Even k) (A B C D j : ℝ) (hC : C≠0)
    (hdet : 0<A*D-B*C) (hj : C*j+D≠0) (χ : ℂ)
    (hF : ∀ z : ℂ, 0<z.im → fourier a z=
      χ/(((C:ℂ)*z+(D:ℂ))^k)*fourier a (((A:ℂ)*z+(B:ℂ))/((C:ℂ)*z+(D:ℂ)))) :
    let L := C^2/(A*D-B*C)
    let r := j+D/C
    let χ₀ := χ*((Real.sqrt L:ℂ)/(C:ℂ))^k
    ∃ bound : ℝ, ∀ M : ℕ,
      AnalyticOnNhd ℂ (mellin (twoError k (coefficients a (-D/C))
        (coefficients a (A/C)) L r χ₀ M)) {s : ℂ | bound-(M:ℝ)<s.re} ∧
      QuantitativeArithmeticMellinStrip.BoundedSubstrips (bound-(M:ℝ))
        (mellin (twoError k (coefficients a (-D/C)) (coefficients a (A/C)) L r χ₀ M)) ∧
      ∀ s : ℂ, bound<s.re →
        transform a j s-χ₀*((L*r^2:ℝ):ℂ)^(s-((k:ℂ)/2))*
          (∑ n∈Finset.range M, (I*(L:ℂ)*(r:ℂ))^n*
            Ring.choose (s+(n:ℂ)-(k:ℂ)) n*
            transform a ((A*j+B)/(C*j+D)) (s+(n:ℂ))) =
          mellin (twoError k (coefficients a (-D/C)) (coefficients a (A/C)) L r χ₀ M) s := by
  dsimp only
  have hL : 0<C^2/(A*D-B*C) := div_pos (sq_pos_of_ne_zero hC) hdet
  have hr : j+D/C≠0 := by
    intro h
    apply hj
    calc C*j+D=C*(j+D/C) := by field_simp
         _=0 := by rw [h,mul_zero]
  obtain ⟨bound,hbound⟩ := matrix_taylor_bounded_rows ha ha0 k A B C D hC hdet χ hF (j+D/C) hr
  refine ⟨bound,fun M => ⟨(hbound M).1,(hbound M).2.1,?_⟩⟩
  intro s hs
  have he := (hbound M).2.2 s hs
  rw [normalized_taylor_sum hL hr k hk] at he
  simp only [normalizedTaylorSum,transform_translate] at he
  rw [show -D/C+(j+D/C)=j by ring,
    matrix_partner A B C D j hC hdet.ne' hj] at he
  exact he
#print axioms matrix_normalized_bounded_rows
end QuantitativeArithmeticTwoSequenceTaylor
end
end

/-! ## QuantitativeArithmeticMatrixEvenRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticTwoSequenceTaylor
open SmallLevelTaylor SmallLevelAdditive Complex Set MeasureTheory
open FinitenessPolynomialSeries FinitenessFourierConstruction

theorem matrix_even_scalar (m : ℕ) (C d : ℝ) (hC : C≠0) (hd : 0<d) (μ : ℂ) :
    (μ*(d:ℂ)^m)*((Real.sqrt (C^2/d):ℂ)/(C:ℂ))^(2*m)=μ := by
  have hc : (C:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hC
  have hd0 : (d:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hd.ne'
  have hs : (Real.sqrt (C^2/d):ℂ)^2=((C^2/d:ℝ):ℂ) := by
    exact_mod_cast Real.sq_sqrt (div_nonneg (sq_nonneg C) hd.le)
  rw [pow_mul,div_pow,hs]
  push_cast
  field_simp
  rw [one_div,inv_pow,mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ hd0),mul_one]

theorem matrix_rate (A B C D j : ℝ) (hC : C≠0) :
    (C^2/(A*D-B*C))*(j+D/C)^2=(C*j+D)^2/(A*D-B*C) := by
  field_simp

theorem matrix_derivative_rate (A B C D j : ℝ) (hC : C≠0) :
    (C^2/(A*D-B*C))*(j+D/C)=C*(C*j+D)/(A*D-B*C) := by
  field_simp

/-- Explicit normalized matrix rows: the leading coefficient is exactly
mu times the positive geometric rate to s-m, with no unknown scalar. -/
theorem matrix_even_rows {a : ℕ → ℂ} (ha : PolynomialBound a) (ha0 : a 0=0)
    (m : ℕ) (A B C D j : ℝ) (hC : C≠0)
    (hdet : 0<A*D-B*C) (hj : C*j+D≠0) (μ : ℂ)
    (hF : ∀ z : ℂ, 0<z.im → fourier a z=
      (μ*((A*D-B*C:ℝ):ℂ)^m)/(((C:ℂ)*z+(D:ℂ))^(2*m))*
        fourier a (((A:ℂ)*z+(B:ℂ))/((C:ℂ)*z+(D:ℂ)))) :
    ∃ (bound : ℝ) (error : ℕ → ℂ → ℂ), ∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | bound-(M:ℝ)<s.re} ∧
      ∀ s : ℂ, bound<s.re →
        transform a j s-μ*(((C*j+D)^2/(A*D-B*C):ℝ):ℂ)^(s-(m:ℂ))*
          (∑ n∈Finset.range M, (I*((C*(C*j+D)/(A*D-B*C):ℝ):ℂ))^n*
            Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n*
            transform a ((A*j+B)/(C*j+D)) (s+(n:ℂ))) = error M s := by
  obtain ⟨bound,hbound⟩ := matrix_normalized_rows ha ha0 (2*m) (even_two_mul m)
    A B C D j hC hdet hj (μ*((A*D-B*C:ℝ):ℂ)^m) hF
  simp only [matrix_even_scalar m C (A*D-B*C) hC hdet μ] at hbound
  refine ⟨bound,_,fun M => ⟨(hbound M).1,?_⟩⟩
  intro s hs
  have he := (hbound M).2 s hs
  rw [matrix_rate A B C D j hC] at he
  have hd : I*((C^2/(A*D-B*C):ℝ):ℂ)*((j+D/C:ℝ):ℂ)=
      I*((C*(C*j+D)/(A*D-B*C):ℝ):ℂ) := by
    rw [mul_assoc,← Complex.ofReal_mul,matrix_derivative_rate A B C D j hC]
  simp only [hd] at he
  have hk : ((2*m:ℕ):ℂ)/2=(m:ℂ) := by push_cast; ring
  rw [hk] at he
  exact he
#print axioms matrix_even_rows
end QuantitativeArithmeticTwoSequenceTaylor
end
end

/-! ## QuantitativeArithmeticMatrixEvenBoundedRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticTwoSequenceTaylor
open SmallLevelTaylor SmallLevelAdditive Complex Set MeasureTheory
open FinitenessPolynomialSeries FinitenessFourierConstruction
/-- Explicit normalized matrix rows: the leading coefficient is exactly
mu times the positive geometric rate to s-m, with no unknown scalar. -/
theorem matrix_even_bounded_rows {a : ℕ → ℂ} (ha : PolynomialBound a) (ha0 : a 0=0)
    (m : ℕ) (A B C D j : ℝ) (hC : C≠0)
    (hdet : 0<A*D-B*C) (hj : C*j+D≠0) (μ : ℂ)
    (hF : ∀ z : ℂ, 0<z.im → fourier a z=
      (μ*((A*D-B*C:ℝ):ℂ)^m)/(((C:ℂ)*z+(D:ℂ))^(2*m))*
        fourier a (((A:ℂ)*z+(B:ℂ))/((C:ℂ)*z+(D:ℂ)))) :
    ∃ (bound : ℝ) (error : ℕ → ℂ → ℂ), ∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | bound-(M:ℝ)<s.re} ∧
      QuantitativeArithmeticMellinStrip.BoundedSubstrips (bound-(M:ℝ)) (error M) ∧
      ∀ s : ℂ, bound<s.re →
        transform a j s-μ*(((C*j+D)^2/(A*D-B*C):ℝ):ℂ)^(s-(m:ℂ))*
          (∑ n∈Finset.range M, (I*((C*(C*j+D)/(A*D-B*C):ℝ):ℂ))^n*
            Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n*
            transform a ((A*j+B)/(C*j+D)) (s+(n:ℂ))) = error M s := by
  obtain ⟨bound,hbound⟩ := matrix_normalized_bounded_rows ha ha0 (2*m) (even_two_mul m)
    A B C D j hC hdet hj (μ*((A*D-B*C:ℝ):ℂ)^m) hF
  simp only [matrix_even_scalar m C (A*D-B*C) hC hdet μ] at hbound
  refine ⟨bound,_,fun M => ⟨(hbound M).1,(hbound M).2.1,?_⟩⟩
  intro s hs
  have he := (hbound M).2.2 s hs
  rw [matrix_rate A B C D j hC] at he
  have hd : I*((C^2/(A*D-B*C):ℝ):ℂ)*((j+D/C:ℝ):ℂ)=
      I*((C*(C*j+D)/(A*D-B*C):ℝ):ℂ) := by
    rw [mul_assoc,← Complex.ofReal_mul,matrix_derivative_rate A B C D j hC]
  simp only [hd] at he
  have hk : ((2*m:ℕ):ℂ)/2=(m:ℂ) := by push_cast; ring
  rw [hk] at he
  exact he
#print axioms matrix_even_bounded_rows
end QuantitativeArithmeticTwoSequenceTaylor
end
end
