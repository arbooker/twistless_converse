module

public import AsymptoticCylinderAnalyticV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCylinder

open MeasureTheory Set AsymptoticFourierNorm InnerProductSpace
open scoped InnerProduct

/-- Cusp coefficient sequences of a fixed polynomial degree. The constant
may depend on the sequence. This is an actual complex vector space. -/
def coefficientSpace (d : ℕ) : Submodule ℂ (ℕ → ℂ) where
  carrier := {a | a 0=0 ∧ ∃ A : ℝ, 0≤A ∧ ∀ n : ℕ, 0<n → ‖a n‖≤A*(n:ℝ)^d}
  zero_mem' := ⟨rfl,0,le_rfl,fun _ _ => by simp⟩
  add_mem' := by
    rintro a b ⟨ha0,A,hA,ha⟩ ⟨hb0,B,hB,hb⟩
    refine ⟨by simp [ha0,hb0],A+B,add_nonneg hA hB,?_⟩
    intro n hn
    calc
      ‖(a+b) n‖≤‖a n‖+‖b n‖ := norm_add_le _ _
      _ ≤ A*(n:ℝ)^d+B*(n:ℝ)^d := add_le_add (ha n hn) (hb n hn)
      _ = (A+B)*(n:ℝ)^d := by ring
  smul_mem' := by
    rintro c a ⟨ha0,A,hA,ha⟩
    refine ⟨by simp [ha0],‖c‖*A,mul_nonneg (norm_nonneg _) hA,?_⟩
    intro n hn
    calc
      ‖(c • a) n‖=‖c‖*‖a n‖ := norm_smul c (a n)
      _ ≤ ‖c‖*(A*(n:ℝ)^d) := mul_le_mul_of_nonneg_left (ha n hn) (norm_nonneg _)
      _ = (‖c‖*A)*(n:ℝ)^d := by ring

theorem coefficientSpace_polynomial (d : ℕ) (a : coefficientSpace d) :
    FinitenessPolynomialSeries.PolynomialBound a.val := by
  obtain ⟨ha0,A,hA,ha⟩ := a.property
  refine ⟨A,hA,d,?_⟩
  intro n
  rcases n with _ | n
  · simp only [ha0,norm_zero]
    positivity
  · exact (ha (n+1) (by omega)).trans (by nlinarith)

theorem coefficientSpace_summable (m t d : ℕ) {scale ε : ℝ}
    (hs : 0<scale) (hε : 0<ε) (hdegree : 2*d+4≤m+2*t+1)
    (a : coefficientSpace d) : Summable (fun n => a.val (n+1) • modeLp m t n hs hε) := by
  obtain ⟨_,A,hA,ha⟩ := a.property
  exact Summable.of_norm
    (coefficient_modes_summable_norm m t d hs hε hA hdegree a.val (fun n => ha (n+1) (by omega)))

/-- The Fourier series defines a complex linear map into the concrete
holomorphic cylinder space. The degree inequality guarantees convergence. -/
noncomputable def fourierMap (m t d : ℕ) {scale ε : ℝ}
    (hs : 0<scale) (hε : 0<ε) (hdegree : 2*d+4≤m+2*t+1) :
    coefficientSpace d →ₗ[ℂ] holomorphicSpace m t hs hε where
  toFun a := ⟨fourierSum m t hs hε a.val,fourierSum_mem m t hs hε a.val⟩
  map_add' a b := by
    apply Subtype.ext
    change (∑' n,(a.val (n+1)+b.val (n+1)) • modeLp m t n hs hε)=
      (∑' n,a.val (n+1) • modeLp m t n hs hε)+(∑' n,b.val (n+1) • modeLp m t n hs hε)
    simp only [add_smul]
    exact (coefficientSpace_summable m t d hs hε hdegree a).tsum_add
      (coefficientSpace_summable m t d hs hε hdegree b)
  map_smul' c a := by
    apply Subtype.ext
    change (∑' n,(c*a.val (n+1)) • modeLp m t n hs hε)=
      c • (∑' n,a.val (n+1) • modeLp m t n hs hε)
    simp only [mul_smul]
    exact (coefficientSpace_summable m t d hs hε hdegree a).tsum_const_smul c

/-- Taking a Fourier inner product recovers the original coefficient,
multiplied by the strictly positive radial norm. -/
theorem fourierSum_inner (m t d n : ℕ) {scale ε : ℝ}
    (hs : 0<scale) (hε : 0<ε) (hdegree : 2*d+4≤m+2*t+1)
    (a : coefficientSpace d) :
    ⟪modeLp m t n hs hε,fourierSum m t hs hε a.val⟫_ℂ=
      a.val (n+1)*(beta m t (scale*(n+1:ℕ)) ε:ℂ) := by
  have ht := (innerSL ℂ (modeLp m t n hs hε)).map_tsum
    (coefficientSpace_summable m t d hs hε hdegree a)
  simp only [innerSL_apply_apply] at ht
  change ⟪modeLp m t n hs hε,∑' j,a.val (j+1) • modeLp m t j hs hε⟫_ℂ=_
  rw [ht]
  rw [tsum_eq_single n]
  · rw [inner_smul_right,inner_self_eq_norm_sq_to_K]
    change a.val (n+1)*(‖modeLp m t n hs hε‖:ℂ)^2=_
    rw [← Complex.ofReal_pow,modeLp_norm_sq]
  · intro j hj
    simp only [inner_smul_right,modeLp_inner_zero m t (Ne.symm hj) hs hε,mul_zero]

/-- No Fourier coefficients are lost by passage to L² equivalence classes. -/
theorem fourierMap_injective (m t d : ℕ) {scale ε : ℝ}
    (hs : 0<scale) (hε : 0<ε) (hdegree : 2*d+4≤m+2*t+1) :
    Function.Injective (fourierMap m t d hs hε hdegree) := by
  intro a b hab
  have he : fourierSum m t hs hε a.val=fourierSum m t hs hε b.val := congrArg Subtype.val hab
  apply Subtype.ext
  funext n
  rcases n with _ | n
  · exact a.property.1.trans b.property.1.symm
  · have hh := congrArg (fun w : Space => ⟪modeLp m t n hs hε,w⟫_ℂ) he
    rw [fourierSum_inner m t d n hs hε hdegree a,fourierSum_inner m t d n hs hε hdegree b] at hh
    apply mul_right_cancel₀ _ hh
    exact_mod_cast (beta_pos m t (mul_pos hs (by positivity : (0:ℝ)<(n+1:ℕ))) hε).ne'

/-- The linear embedding agrees with the original analytic function
almost everywhere, with no coefficient-growth hypothesis left to supply. -/
theorem fourierMap_eq_disk_ae (h t d : ℕ) {ε : ℝ} (hε : 0<ε)
    (hd : 2*d+4≤2*h+2*t+1) (a : coefficientSpace d) :
    ((fourierMap (2*h) t d (by positivity) hε hd a :
      holomorphicSpace (2*h) t (by positivity : 0<4*Real.pi) hε):Space) =ᵐ[measure]
      (fun z => (z.2^h*(min (z.2/ε) 1)^t:ℝ)*FinitenessPolynomialSeries.sum a.val (qCylinder z)) := by
  obtain ⟨ha0,A,hA,ha⟩ := a.property
  exact fourierSum_eq_disk_ae h t d hε hA hd a.val ha0
    (fun n => ha (n+1) (by omega)) (coefficientSpace_polynomial d a)

#print axioms fourierMap
#print axioms fourierSum_inner
#print axioms fourierMap_injective
#print axioms fourierMap_eq_disk_ae

end AsymptoticCylinder
