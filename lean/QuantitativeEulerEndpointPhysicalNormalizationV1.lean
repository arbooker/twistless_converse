module

public import QuantitativeEulerEndpointActualReplacementRowsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPhysicalNormalization
open ContinuousLinearMap QuantitativeEulerEndpointBlockNormalization
open scoped Classical

theorem pi_conversion_norm_ge_one {ι J : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup J] [NormedSpace ℂ J] [Nontrivial J] :
    1≤‖(PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => J)).symm.toContinuousLinearMap‖ := by
  obtain ⟨v,hv⟩ := exists_ne (0:J)
  let T := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => J)).symm.toContinuousLinearMap
  let f : ι → J := fun _ => v
  have hf : ‖f‖≤‖v‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr (fun _ => le_rfl)
  have he : ‖v‖≤‖T f‖ := PiLp.norm_apply_le (T f) (Classical.arbitrary ι)
  have hh := he.trans ((T.le_opNorm f).trans (mul_le_mul_of_nonneg_left hf (norm_nonneg T)))
  have hv0 : 0<‖v‖ := norm_pos_iff.mpr hv
  nlinarith

theorem baseline_square_le {ι : Type*} [Fintype ι] (b : ι → ℝ) (hb : ∀ i,0≤b i)
    {d : ℝ} (hd : 1≤d) : (∑ i,(b i)^2)≤(d*∑ i,b i)^2 := by
  have hs := Finset.sum_nonneg (fun i (_ : i∈Finset.univ) => hb i)
  have hh : (∑ i,b i)≤d*∑ i,b i := by nlinarith
  exact (Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hb i)).trans (pow_le_pow_left₀ hs hh 2)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem gram_sum_norm {ι : Type*} [Fintype ι] (E : ι → H →L[ℂ] H)
    (b : ι → ℝ) (hb : ∀ i,‖E i‖≤b i) (U : H →L[ℂ] H) (hU : ‖U‖≤1)
    {r : ℝ} (hr : 0≤r) :
    ‖∑ i,star ((r:ℂ) • (E i*U))*((r:ℂ) • (E i*U))‖≤r^2*∑ i,(b i)^2 := by
  have hn (i : ι) : ‖(r:ℂ) • (E i*U)‖≤r*b i := by
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr]
    apply mul_le_mul_of_nonneg_left _ hr
    exact (norm_mul_le _ _).trans ((mul_le_mul (hb i) hU (norm_nonneg U)
      ((norm_nonneg _).trans (hb i))).trans_eq (mul_one _))
  calc
    _ ≤ ∑ i,‖star ((r:ℂ) • (E i*U))*((r:ℂ) • (E i*U))‖ := norm_sum_le _ _
    _ ≤ ∑ i,(r*b i)^2 := Finset.sum_le_sum (fun i _ => by
      rw [CStarRing.norm_star_mul_self,←pow_two]
      exact pow_le_pow_left₀ (norm_nonneg _) (hn i) 2)
    _ = _ := by simp only [mul_pow,Finset.mul_sum]

/-- The same real normalization controls a physical Gram whenever the
unscaled row square sum is bounded by the stored normalization square sum. -/
theorem combined_order {ι κ : Type*} [Fintype ι] [Fintype κ]
    (E : ι → H →L[ℂ] H) (F : κ → H →L[ℂ] H) (b : ι → ℝ) (c : κ → ℝ)
    (hb : ∀ i,‖E i‖≤b i) (hc : ∀ i,‖F i‖≤c i)
    (C : ℕ → ℝ) (n : ℕ) (hs : (∑ i,(b i)^2)+(∑ i,(c i)^2)≤∑ i : Fin n,(C i)^2)
    (U : H →L[ℂ] H) (hU : ‖U‖≤1) :
    let r := factor C n
    let G := (∑ i,star ((r:ℂ) • (E i*U))*((r:ℂ) • (E i*U)))+
      ∑ i,star ((r:ℂ) • (F i*U))*((r:ℂ) • (F i*U))
    0≤G ∧ G≤1 := by
  intro r G
  have hr : 0≤r := (factor_pos C n).le
  have hp : 0≤G := add_nonneg (Finset.sum_nonneg (fun _ _ => star_mul_self_nonneg _))
    (Finset.sum_nonneg (fun _ _ => star_mul_self_nonneg _))
  have hn : ‖G‖≤1 := by
    have he := gram_sum_norm E b hb U hU hr
    have hf := gram_sum_norm F c hc U hU hr
    have hg := (norm_add_le _ _).trans (add_le_add he hf)
    have hs' := mul_le_mul_of_nonneg_left hs (sq_nonneg r)
    have hnorm := normalized_square_sum C n
    simp only [mul_pow,←Finset.mul_sum] at hnorm
    change r^2*(∑ i : Fin n,(C i)^2)≤1 at hnorm
    exact hg.trans (by nlinarith only [hs',hnorm])
  exact ⟨hp,(CStarAlgebra.norm_le_one_iff_of_nonneg _ hp).mp hn⟩

#print axioms pi_conversion_norm_ge_one
#print axioms baseline_square_le
#print axioms gram_sum_norm
#print axioms combined_order
end QuantitativeEulerEndpointPhysicalNormalization
