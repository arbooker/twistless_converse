module

public import QuantitativeMaassHilbertSchmidtIdealV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section

namespace QuantitativeMaass

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def linearPacketTrace (b : HilbertBasis ι ℂ H) (B T : H→L[ℂ]H) : ℝ :=
  ∑' i,(inner ℂ (T (B.adjoint (b i))) (B.adjoint (b i))).re

omit [CompleteSpace H] in
theorem linearPacketTrace_column_bound (T : H→L[ℂ]H) (x : H) :
    ‖(inner ℂ (T x) x).re‖≤‖T‖*‖x‖^2 := by
  calc
    _ ≤ ‖inner ℂ (T x) x‖ := by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (inner ℂ (T x) x)
    _ ≤ ‖T x‖*‖x‖ := norm_inner_le_norm _ _
    _ ≤ (‖T‖*‖x‖)*‖x‖ := mul_le_mul_of_nonneg_right (T.le_opNorm x) (norm_nonneg _)
    _ = _ := by ring

theorem linearPacketTrace_summable (b : HilbertBasis ι ℂ H) (B T : H→L[ℂ]H)
    (hB : Summable (fun i => ‖B (b i)‖^2)) :
    Summable (fun i => (inner ℂ (T (B.adjoint (b i))) (B.adjoint (b i))).re) := by
  apply Summable.of_norm_bounded ((adjoint_energy_eq b B hB).1.mul_left ‖T‖)
  intro i
  exact linearPacketTrace_column_bound T _

theorem linearPacketTrace_bound (b : HilbertBasis ι ℂ H) (B T : H→L[ℂ]H)
    (hB : Summable (fun i => ‖B (b i)‖^2)) :
    |linearPacketTrace b B T|≤‖T‖*hilbertSchmidtEnergy b B := by
  obtain ⟨ha,he⟩ := adjoint_energy_eq b B hB
  have hh := tsum_of_norm_bounded (ha.mul_left ‖T‖).hasSum
    (fun i => linearPacketTrace_column_bound T (B.adjoint (b i)))
  rw [ha.tsum_mul_left] at hh
  change ‖linearPacketTrace b B T‖≤‖T‖*hilbertSchmidtEnergy b B.adjoint at hh
  rw [he,Real.norm_eq_abs] at hh
  exact hh

theorem linearPacketTrace_sub (b : HilbertBasis ι ℂ H) (B T S : H→L[ℂ]H)
    (hB : Summable (fun i => ‖B (b i)‖^2)) :
    linearPacketTrace b B (T-S)=linearPacketTrace b B T-linearPacketTrace b B S := by
  simp only [linearPacketTrace,sub_apply,inner_sub_left,Complex.sub_re]
  exact (linearPacketTrace_summable b B T hB).tsum_sub (linearPacketTrace_summable b B S hB)

/-- Linear trace approximation requires no positivity of the approximant. -/
theorem linearPacketTrace_approx (b : HilbertBasis ι ℂ H) (B T S : H→L[ℂ]H)
    (hB : Summable (fun i => ‖B (b i)‖^2)) {δ : ℝ} (hδ : ‖T-S‖≤δ) :
    |linearPacketTrace b B T-linearPacketTrace b B S|≤δ*hilbertSchmidtEnergy b B := by
  rw [←linearPacketTrace_sub b B T S hB]
  exact (linearPacketTrace_bound b B (T-S) hB).trans
    (mul_le_mul_of_nonneg_right hδ (tsum_nonneg (fun _ => sq_nonneg _)))

theorem linearPacketTrace_projection (b : HilbertBasis ι ℂ H) (B : H→L[ℂ]H)
    (hB : Summable (fun i => ‖B (b i)‖^2)) (W : Submodule ℂ H) [W.HasOrthogonalProjection] :
    linearPacketTrace b B W.starProjection=hilbertSchmidtEnergy b (B.comp W.starProjection) := by
  have hs := (right_comp_energy_bound b B W.starProjection hB).1
  have he := (adjoint_energy_eq b (B.comp W.starProjection) hs).2
  rw [ContinuousLinearMap.adjoint_comp,(isSelfAdjoint_starProjection W).adjoint_eq] at he
  rw [←he]
  apply tsum_congr
  intro i
  exact W.re_inner_starProjection_eq_normSq (B.adjoint (b i))

#print axioms linearPacketTrace_column_bound
#print axioms linearPacketTrace_summable
#print axioms linearPacketTrace_bound
#print axioms linearPacketTrace_sub
#print axioms linearPacketTrace_approx
#print axioms linearPacketTrace_projection

end QuantitativeMaass
