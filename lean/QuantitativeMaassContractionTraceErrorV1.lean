module

public import QuantitativeMaassQuadraticTraceErrorV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

namespace QuantitativeMaass

/-- For two families in the unit ball, the quadratic observation error
is controlled linearly by their squared difference energy. -/
theorem contraction_quadratic_trace_error {H ι : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype ι]
    (T : H →L[ℂ] H) (hT : ‖T‖≤1) (v w : ι → H)
    (hv : ∀ i,‖v i‖≤1) (hw : ∀ i,‖w i‖≤1) :
    (∑ i,((inner ℂ (T (w i)) (w i)).re-(inner ℂ (T (v i)) (v i)).re))^2≤
      16*(Fintype.card ι:ℝ)*(∑ i,‖w i-v i‖^2) := by
  classical
  let V := ∑ i,‖v i‖^2
  let E := ∑ i,‖w i-v i‖^2
  have hV : V≤(Fintype.card ι:ℝ) := by
    have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) =>
      pow_le_pow_left₀ (norm_nonneg _) (hv i) 2)
    simpa only [one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using hh
  have hE : E≤4*(Fintype.card ι:ℝ) := by
    have hi (i : ι) : ‖w i-v i‖^2≤4 := by
      have hnorm := (norm_sub_le (w i) (v i)).trans (add_le_add (hw i) (hv i))
      nlinarith [norm_nonneg (w i-v i)]
    have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hi i)
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm] using hh
  have hV0 : 0≤V := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hE0 : 0≤E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hT2 : ‖T‖^2≤1 := by nlinarith [norm_nonneg T]
  have hfirst : 8*‖T‖^2*V*E≤8*(Fintype.card ι:ℝ)*E := by
    have hh := mul_le_mul hT2 hV hV0 (by norm_num : (0:ℝ)≤1)
    have hh' := mul_le_mul_of_nonneg_right hh hE0
    nlinarith only [hh']
  have hsecond : 2*‖T‖^2*E^2≤8*(Fintype.card ι:ℝ)*E := by
    have hh := mul_le_mul_of_nonneg_right hT2 (sq_nonneg E)
    have he := mul_le_mul_of_nonneg_right hE hE0
    nlinarith only [hh,he]
  have hh := finite_quadratic_trace_error T v w
  change _≤8*‖T‖^2*V*E+2*‖T‖^2*E^2 at hh
  change _≤16*(Fintype.card ι:ℝ)*E
  linarith

#print axioms contraction_quadratic_trace_error

end QuantitativeMaass
