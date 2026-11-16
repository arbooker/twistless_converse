module

public import QuantitativeMaassHilbertSchmidtV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open scoped BigOperators

namespace QuantitativeMaass

variable {F ι : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Quadratic observations of a perturbed vector require only the norm
of the observation, not positivity or symmetry. -/
theorem quadratic_observation_error (T : F →L[ℂ] F) (v w : F) :
    |(inner ℂ (T w) w).re-(inner ℂ (T v) v).re| ≤
      ‖T‖*(2*‖v‖*‖w-v‖+‖w-v‖^2) := by
  have he : inner ℂ (T w) w-inner ℂ (T v) v=
      inner ℂ (T (w-v)) w+inner ℂ (T v) (w-v) := by
    rw [map_sub,inner_sub_left,inner_sub_right]
    ring
  have hw : ‖w‖≤‖v‖+‖w-v‖ := by
    have hh := norm_add_le v (w-v)
    have heq : v+(w-v)=w := by abel
    rw [heq] at hh
    exact hh
  calc
    _ = |(inner ℂ (T (w-v)) w+inner ℂ (T v) (w-v)).re| := by
      rw [←he,Complex.sub_re]
    _ ≤ ‖inner ℂ (T (w-v)) w+inner ℂ (T v) (w-v)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖inner ℂ (T (w-v)) w‖+‖inner ℂ (T v) (w-v)‖ := norm_add_le _ _
    _ ≤ ‖T (w-v)‖*‖w‖+‖T v‖*‖w-v‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ (‖T‖*‖w-v‖)*(‖v‖+‖w-v‖)+(‖T‖*‖v‖)*‖w-v‖ := by
      exact add_le_add (mul_le_mul (T.le_opNorm _) hw (norm_nonneg _) (by positivity))
        (mul_le_mul_of_nonneg_right (T.le_opNorm _) (norm_nonneg _))
    _ = _ := by ring

/-- A finite quadratic trace comparison uses squared error and the
energy of the exact family. No norm bound on the approximating family
and no factor from its ambient Hilbert-space dimension are introduced. -/
theorem finite_quadratic_trace_error [Fintype ι] (T : F →L[ℂ] F) (v w : ι → F) :
    (∑ i,((inner ℂ (T (w i)) (w i)).re-(inner ℂ (T (v i)) (v i)).re))^2 ≤
      8*‖T‖^2*(∑ i,‖v i‖^2)*(∑ i,‖w i-v i‖^2)+
        2*‖T‖^2*(∑ i,‖w i-v i‖^2)^2 := by
  classical
  let S : ℝ := ∑ i,‖v i‖*‖w i-v i‖
  let E : ℝ := ∑ i,‖w i-v i‖^2
  have he : 0≤E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs : 0≤S := Finset.sum_nonneg (fun _ _ => by positivity)
  have hc : S^2≤(∑ i,‖v i‖^2)*E :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖v i‖) (fun i => ‖w i-v i‖)
  have ht : |∑ i,((inner ℂ (T (w i)) (w i)).re-(inner ℂ (T (v i)) (v i)).re)|≤
      ‖T‖*(2*S+E) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => quadratic_observation_error T (v i) (w i))
    apply hh.trans_eq
    simp only [S,E,Finset.mul_sum,Finset.sum_add_distrib,mul_add,mul_assoc]
  have hsq := pow_le_pow_left₀ (abs_nonneg _) ht 2
  rw [sq_abs,mul_pow] at hsq
  have hp := mul_le_mul_of_nonneg_left hc (by positivity : 0≤8*‖T‖^2)
  have hm := mul_nonneg (sq_nonneg ‖T‖) (sq_nonneg (2*S-E))
  change _≤8*‖T‖^2*(∑ i,‖v i‖^2)*E+2*‖T‖^2*E^2
  nlinarith [hp]

#print axioms quadratic_observation_error
#print axioms finite_quadratic_trace_error

end QuantitativeMaass
