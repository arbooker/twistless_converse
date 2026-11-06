module

public import QuantitativeEulerEndpointPhysicalCornerV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointNestedOperator
open Polynomial QuantitativeEulerEndpointBernstein QuantitativeEulerEndpointSoftUpdate

variable {𝔄 : Type*} [CStarAlgebra 𝔄] [PartialOrder 𝔄] [StarOrderedRing 𝔄]

theorem scaled_energy_order (G : 𝔄) (b : ℝ) (hb : 0<b) (hG : 0≤G ∧ G≤b • 1) :
    0≤b⁻¹ • G ∧ b⁻¹ • G≤1 := by
  refine ⟨smul_nonneg (inv_nonneg.mpr hb.le) hG.1,?_⟩
  have hh := smul_le_smul_of_nonneg_left hG.2 (inv_nonneg.mpr hb.le)
  simpa only [smul_smul,inv_mul_cancel₀ hb.ne',one_smul] using hh

/-- The common nested polynomial formula, on a unital source algebra. -/
def filter (G₀ : 𝔄) (G : ℕ → 𝔄) (q₀ : ℝ[X]) (d : ℕ → ℕ) (q : ℕ → ℝ[X]) : ℕ → 𝔄
  | 0 => aeval G₀ q₀
  | j+1 => let F := filter G₀ G q₀ d q j
    aeval (update F (F*G j*F) (d j)) (q j)

theorem filter_order (G₀ : 𝔄) (G : ℕ → 𝔄) (q₀ : ℝ[X]) (d : ℕ → ℕ) (q : ℕ → ℝ[X])
    (h₀ : 0≤G₀ ∧ G₀≤1) (hG : ∀ j,0≤G j ∧ G j≤1)
    (hq₀ : ScalarInitializer q₀) (hq : ∀ j,ScalarSharpening (q j)) (n : ℕ) :
    0≤filter G₀ G q₀ d q n ∧ filter G₀ G q₀ d q n≤1 := by
  induction n with
  | zero => exact scalar_initializer_order hq₀ G₀ h₀.1 h₀.2
  | succ n ih =>
    let F := filter G₀ G q₀ d q n
    have he : 0≤F*G n*F ∧ F*G n*F≤1 := by
      simpa only [inv_one,one_smul] using compressed_energy_order F (G n) ih.1 ih.2
        (hG n).1 (by norm_num : (0:ℝ)<1) (by simpa only [one_smul] using (hG n).2)
    have hu := update_order F (F*G n*F) ih.1 ih.2 he.1 he.2 (d n)
    have hz := scalar_sharpening_order (hq n) _ hu.1 (hu.2.trans ih.2)
    exact ⟨hz.1,hz.2.trans (hu.2.trans ih.2)⟩

theorem filter_step_le (G₀ : 𝔄) (G : ℕ → 𝔄) (q₀ : ℝ[X]) (d : ℕ → ℕ) (q : ℕ → ℝ[X])
    (h₀ : 0≤G₀ ∧ G₀≤1) (hG : ∀ j,0≤G j ∧ G j≤1)
    (hq₀ : ScalarInitializer q₀) (hq : ∀ j,ScalarSharpening (q j)) (n : ℕ) :
    filter G₀ G q₀ d q (n+1)≤filter G₀ G q₀ d q n := by
  let F := filter G₀ G q₀ d q n
  have hf := filter_order G₀ G q₀ d q h₀ hG hq₀ hq n
  have he : 0≤F*G n*F ∧ F*G n*F≤1 := by
    simpa only [inv_one,one_smul] using compressed_energy_order F (G n) hf.1 hf.2
      (hG n).1 (by norm_num : (0:ℝ)<1) (by simpa only [one_smul] using (hG n).2)
  have hu := update_order F (F*G n*F) hf.1 hf.2 he.1 he.2 (d n)
  exact (scalar_sharpening_order (hq n) _ hu.1 (hu.2.trans hf.2)).2.trans hu.2

section Vectors
open ContinuousLinearMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem polynomial_apply_eigen (T : E →L[ℂ] E) (v : E) (c : ℝ)
    (hv : T v=c • v) (q : ℝ[X]) : aeval T q v=q.eval c • v := by
  have hp (n : ℕ) : (T^n) v=c^n • v := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ',mul_apply_eq_comp,ih,map_smul_of_tower,hv,smul_smul]
      rw [pow_succ]
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,add_apply,hp,hq,eval_add,add_smul]
  | monomial n r =>
    simp only [aeval_monomial,Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul,
      smul_apply,hp,smul_smul,eval_monomial]

theorem update_apply_fixed (F G : E →L[ℂ] E) (v : E)
    (hF : F v=v) (hG : G v=0) (d : ℕ) : QuantitativeEulerEndpointSoftUpdate.update F (F*G*F) d v=v := by
  have h1 (w : E) : (1 : E →L[ℂ] E) w=w := rfl
  have he : (F*G*F) v=0 := by simp only [mul_apply_eq_comp,hF,hG,map_zero]
  have hs : (1-F*G*F) v=v := by simp only [sub_apply,he,h1,sub_zero]
  have hp (n : ℕ) : ((1-F*G*F)^n) v=v := by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ',mul_apply_eq_comp,ih,hs]
  simp only [QuantitativeEulerEndpointSoftUpdate.update,sub_apply,mul_apply_eq_comp,hF,hp,h1,sub_self,map_zero,sub_zero]

/-- Exact common zero-energy vectors are fixed by every nested polynomial. -/
theorem filter_apply_fixed (G₀ : E →L[ℂ] E) (G : ℕ → E →L[ℂ] E)
    (q₀ : ℝ[X]) (d : ℕ → ℕ) (q : ℕ → ℝ[X]) (v : E)
    (h₀ : G₀ v=0) (hG : ∀ j,G j v=0) (hq₀ : q₀.eval 0=1)
    (hq : ∀ j,(q j).eval 1=1) (n : ℕ) : filter G₀ G q₀ d q n v=v := by
  induction n with
  | zero =>
    change aeval G₀ q₀ v=v
    rw [polynomial_apply_eigen G₀ v 0 (by simpa only [zero_smul] using h₀),hq₀,one_smul]
  | succ n ih =>
    let F := filter G₀ G q₀ d q n
    change aeval (QuantitativeEulerEndpointSoftUpdate.update F (F*G n*F) (d n)) (q n) v=v
    rw [polynomial_apply_eigen _ v 1
      (by simpa only [one_smul] using update_apply_fixed _ (G n) v ih (hG n) (d n)),hq n,one_smul]

end Vectors
#print axioms filter_order
#print axioms filter_step_le
#print axioms filter_apply_fixed
end QuantitativeEulerEndpointNestedOperator
