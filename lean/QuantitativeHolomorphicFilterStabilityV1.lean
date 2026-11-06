module

public import QuantitativeHolomorphicNewtonPerturbationV1
public import QuantitativePositiveGramFilterV1
public import AsymptoticObservationPerturbationV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open ContinuousLinearMap

variable {G H K ι : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def finiteRowGram (qs : Finset ι) (L : ι → H →L[ℂ] K) (V : G →L[ℂ] H) :=
  ∑ i ∈ qs, ((L i).comp V).adjoint.comp ((L i).comp V)

def finiteRowBound (qs : Finset ι) (b : ι → ℝ) : ℝ := 1 + ∑ i ∈ qs, b i ^ 2

def finiteRowFilter (qs : Finset ι) (L : ι → H →L[ℂ] K) (b : ι → ℝ)
    (V : G →L[ℂ] H) (d : ℕ) := (1 - (finiteRowBound qs b)⁻¹ • finiteRowGram qs L V) ^ d

theorem finiteRowBound_pos (qs : Finset ι) (b : ι → ℝ) : 0 < finiteRowBound qs b := by
  unfold finiteRowBound
  positivity

omit [CompleteSpace G] [CompleteSpace H] [CompleteSpace K] in
private theorem row_comp_norm_le (L : H →L[ℂ] K) (V : G →L[ℂ] H) {b : ℝ}
    (hL : ‖L‖ ≤ b) (hV : ‖V‖ ≤ 1) : ‖L.comp V‖ ≤ b :=
  (opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_left hV (norm_nonneg L)).trans (by simpa using hL))

omit [CompleteSpace H] in
theorem finiteRowGram_bounds (qs : Finset ι) (L : ι → H →L[ℂ] K) (b : ι → ℝ)
    (hL : ∀ i, ‖L i‖ ≤ b i) (V : G →L[ℂ] H) (hV : ‖V‖ ≤ 1) :
    0 ≤ finiteRowGram qs L V ∧ finiteRowGram qs L V ≤ finiteRowBound qs b • 1 := by
  have hg := QuantitativePositiveGramFilter.gram_sum_bounds qs (fun i => (L i).comp V)
  refine ⟨hg.1, hg.2.trans ?_⟩
  apply smul_le_smul_of_nonneg_right _ zero_le_one
  apply add_le_add le_rfl
  exact Finset.sum_le_sum (fun i _ =>
    pow_le_pow_left₀ (norm_nonneg _) (row_comp_norm_le _ _ (hL i) hV) 2)

omit [CompleteSpace H] in
theorem finiteRowFilter_order (qs : Finset ι) (L : ι → H →L[ℂ] K) (b : ι → ℝ)
    (hL : ∀ i, ‖L i‖ ≤ b i) (V : G →L[ℂ] H) (hV : ‖V‖ ≤ 1) (d : ℕ) :
    0 ≤ finiteRowFilter qs L b V d ∧ finiteRowFilter qs L b V d ≤ 1 ∧
      ‖finiteRowFilter qs L b V d‖ ≤ 1 :=
  QuantitativePositiveGramFilter.filter_order _ (finiteRowBound_pos qs b)
    (finiteRowGram_bounds qs L b hL V hV).1 (finiteRowGram_bounds qs L b hL V hV).2 d

omit [CompleteSpace H] in
theorem finiteRowGram_difference (qs : Finset ι) (L : ι → H →L[ℂ] K) (b : ι → ℝ)
    (hL : ∀ i, ‖L i‖ ≤ b i) (U V : G →L[ℂ] H) (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1) :
    ‖finiteRowGram qs L V - finiteRowGram qs L U‖ ≤
      2 * (∑ i ∈ qs, b i ^ 2) * ‖V - U‖ := by
  have hrow (i : ι) :
      ‖((L i).comp V).adjoint.comp ((L i).comp V) -
        ((L i).comp U).adjoint.comp ((L i).comp U)‖ ≤ 2 * b i ^ 2 * ‖V - U‖ := by
    have hb0 : 0 ≤ b i := (norm_nonneg _).trans (hL i)
    have hv := row_comp_norm_le _ _ (hL i) hV
    have hu := row_comp_norm_le _ _ (hL i) hU
    have hd : ‖(L i).comp V - (L i).comp U‖ ≤ b i * ‖V - U‖ := by
      rw [← comp_sub]
      exact (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right (hL i) (norm_nonneg _))
    apply (gram_difference_norm_le ((L i).comp U) ((L i).comp V)).trans
    have hh := mul_le_mul (add_le_add hv hu) hd (norm_nonneg _) (by positivity : 0 ≤ b i + b i)
    exact hh.trans_eq (by ring)
  rw [finiteRowGram, finiteRowGram, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun i _ => hrow i)).trans_eq
  simp only [Finset.sum_mul, Finset.mul_sum]

omit [CompleteSpace H] in
theorem finiteRowFilter_difference (qs : Finset ι) (L : ι → H →L[ℂ] K) (b : ι → ℝ)
    (hL : ∀ i, ‖L i‖ ≤ b i) (U V : G →L[ℂ] H) (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1) (d : ℕ) :
    ‖finiteRowFilter qs L b V d - finiteRowFilter qs L b U d‖ ≤
      (2 * d : ℝ) * ‖V - U‖ := by
  let M := finiteRowBound qs b
  let SU := 1 - M⁻¹ • finiteRowGram qs L U
  let SV := 1 - M⁻¹ • finiteRowGram qs L V
  have hM : 0 < M := finiteRowBound_pos qs b
  have hSU : ‖SU‖ ≤ 1 := by simpa only [finiteRowFilter, pow_one] using (finiteRowFilter_order qs L b hL U hU 1).2.2
  have hSV : ‖SV‖ ≤ 1 := by simpa only [finiteRowFilter, pow_one] using (finiteRowFilter_order qs L b hL V hV 1).2.2
  have hsum : (∑ i ∈ qs, b i ^ 2) ≤ M := by dsimp [M, finiteRowBound]; linarith
  have hgram : ‖finiteRowGram qs L V - finiteRowGram qs L U‖ ≤ 2 * M * ‖V - U‖ :=
    (finiteRowGram_difference qs L b hL U V hU hV).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by norm_num)) (norm_nonneg _))
  have he : SV - SU = M⁻¹ • (finiteRowGram qs L U - finiteRowGram qs L V) := by
    dsimp [SV, SU]
    rw [smul_sub]
    abel
  have hstep : ‖SV - SU‖ ≤ 2 * ‖V - U‖ := by
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hM), norm_sub_rev]
    apply (mul_le_mul_of_nonneg_left hgram (inv_nonneg.2 hM.le)).trans_eq
    field_simp
  have hp := AsymptoticReconstruction.power_difference_norm_le SV SU hSV hSU d
  exact hp.trans ((mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg d)).trans_eq (by ring))

/-- The final ambient positive filter loses only a linear factor in its
degree when the contraction reconstruction is replaced. -/
theorem finiteRowFilter_sandwich_difference (qs : Finset ι) (L : ι → H →L[ℂ] K) (b : ι → ℝ)
    (hL : ∀ i, ‖L i‖ ≤ b i) (U V : G →L[ℂ] H) (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1) (d : ℕ) :
    ‖V.comp ((finiteRowFilter qs L b V d).comp V.adjoint) -
      U.comp ((finiteRowFilter qs L b U d).comp U.adjoint)‖ ≤
      (2 * d + 2 : ℝ) * ‖V - U‖ := by
  have hfv := (finiteRowFilter_order qs L b hL V hV d).2.2
  have hfu := (finiteRowFilter_order qs L b hL U hU d).2.2
  apply (AsymptoticObservation.sandwich_sub_norm_le V U _ _ hfv hfu).trans
  have hnorm : ‖U‖ * ‖V‖ ≤ 1 := by
    simpa using mul_le_mul hU hV (norm_nonneg _) zero_le_one
  have hsum : ‖V‖ + ‖U‖ ≤ 2 := by linarith
  have hh := add_le_add
    (mul_le_mul_of_nonneg_right hsum (norm_nonneg (V - U)))
    (mul_le_mul hnorm (finiteRowFilter_difference qs L b hL U V hU hV d)
      (norm_nonneg _) zero_le_one)
  exact hh.trans_eq (by ring)

#print axioms finiteRowGram_difference
#print axioms finiteRowFilter_difference
#print axioms finiteRowFilter_sandwich_difference

end QuantitativeHolomorphic
