module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Tactic

/-! Consolidated chapter: QuantitativeArithmeticPolynomialRootCover. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticPolynomialRootCoverV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 500000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPolynomialRootCover
open Polynomial Finset

/-- A root cover from the first barycentric interpolation formula.  Unlike
root counting by Rouché, this only uses a finite norm estimate.  The nodes
need not be zeros of the polynomial, and no simplicity of roots is assumed. -/
theorem monic_root_cover {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c : ι → ℂ) (r : ι → ℝ) (P : ℂ[X])
    (hc : Set.InjOn c s) (hP : P.Monic) (hd : P.degree = (s.card : WithBot ℕ))
    (hr : ∀ i ∈ s, 0 < r i)
    (hsmall : ∑ i ∈ s, ‖Lagrange.nodalWeight s c i * P.eval (c i)‖ / r i < 1)
    (z : ℂ) (hz : P.eval z = 0) :
    ∃ i ∈ s, ‖z-c i‖ < r i := by
  by_contra h
  push Not at h
  have haway : ∀ i ∈ s, z ≠ c i := by
    intro i hi heq
    have hle := h i hi
    rw [heq, sub_self, norm_zero] at hle
    exact (not_le_of_gt (hr i hi)) hle
  have hR : (Lagrange.nodal s c).eval z ≠ 0 :=
    Lagrange.eval_nodal_not_at_node haway
  have hdegree : (P - Lagrange.nodal s c).degree < (s.card : WithBot ℕ) := by
    rw [← hd]
    apply Polynomial.degree_sub_lt_left
    · simpa only [Lagrange.degree_nodal] using hd
    · exact hP.ne_zero
    · exact hP.trans (Lagrange.nodal_monic (s := s) (v := c)).symm
  have hinterp : P - Lagrange.nodal s c =
      Lagrange.interpolate s c (fun i => P.eval (c i)) := by
    apply Lagrange.eq_interpolate_of_eval_eq _ hc hdegree
    intro i hi
    rw [Polynomial.eval_sub, Lagrange.eval_nodal_at_node hi, sub_zero]
  have he := congrArg (Polynomial.eval z) hinterp
  rw [Polynomial.eval_sub, hz,
    Lagrange.eval_interpolate_not_at_node _ haway] at he
  have hsum : (∑ i ∈ s,
      Lagrange.nodalWeight s c i * (z-c i)⁻¹ * P.eval (c i)) = -1 := by
    have hzero : (Lagrange.nodal s c).eval z *
        ((∑ i ∈ s, Lagrange.nodalWeight s c i * (z-c i)⁻¹ * P.eval (c i)) + 1) = 0 := by
      linear_combination -he
    have hzero' := (mul_eq_zero.mp hzero).resolve_left hR
    linear_combination hzero'
  have hbound : (1 : ℝ) ≤
      ∑ i ∈ s, ‖Lagrange.nodalWeight s c i * P.eval (c i)‖ / r i := by
    calc
      (1 : ℝ) = ‖∑ i ∈ s,
          Lagrange.nodalWeight s c i * (z-c i)⁻¹ * P.eval (c i)‖ := by
        rw [hsum]
        norm_num
      _ ≤ ∑ i ∈ s,
          ‖Lagrange.nodalWeight s c i * (z-c i)⁻¹ * P.eval (c i)‖ :=
        norm_sum_le _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [show Lagrange.nodalWeight s c i * (z-c i)⁻¹ * P.eval (c i) =
          (Lagrange.nodalWeight s c i * P.eval (c i)) / (z-c i) by
            rw [div_eq_mul_inv]; ring, norm_div]
        exact div_le_div_of_nonneg_left (norm_nonneg _) (hr i hi) (h i hi)
  exact (not_le_of_gt hsmall) hbound

/-- A rational certificate can bound real and imaginary parts instead of
computing square roots.  Each `b i` is the contribution after division by
the disk radius. -/
theorem monic_root_cover_of_coordinate_bounds {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c : ι → ℂ) (r b : ι → ℝ) (P : ℂ[X])
    (hc : Set.InjOn c s) (hP : P.Monic) (hd : P.degree = (s.card : WithBot ℕ))
    (hr : ∀ i ∈ s, 0 < r i)
    (hb : ∀ i ∈ s,
      |(Lagrange.nodalWeight s c i * P.eval (c i)).re| +
        |(Lagrange.nodalWeight s c i * P.eval (c i)).im| ≤ b i * r i)
    (hsmall : ∑ i ∈ s, b i < 1)
    (z : ℂ) (hz : P.eval z = 0) :
    ∃ i ∈ s, ‖z-c i‖ < r i := by
  apply monic_root_cover s c r P hc hP hd hr _ z hz
  apply lt_of_le_of_lt _ hsmall
  apply Finset.sum_le_sum
  intro i hi
  apply (div_le_iff₀ (hr i hi)).mpr
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (hb i hi)

#print axioms monic_root_cover
#print axioms monic_root_cover_of_coordinate_bounds
end QuantitativeArithmeticPolynomialRootCover
end
end

/-! ## QuantitativeArithmeticPolynomialRootSeparationV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticPolynomialRootCover
open Polynomial Finset

/-- A residual bound and lower bounds on node separations control a barycentric
coefficient. This avoids expanding exact complex inverses at large rational nodes. -/
theorem nodal_eval_bound_of_separations {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c : ι → ℂ) (P : ℂ[X]) (i : ι)
    (d : ι → ℝ) (b r : ℝ)
    (hd : ∀ j ∈ s.erase i, 0 < d j)
    (hsep : ∀ j ∈ s.erase i, d j ≤ ‖c i-c j‖)
    (heval : ‖P.eval (c i)‖ ≤ b*r*∏ j ∈ s.erase i, d j) :
    ‖Lagrange.nodalWeight s c i*P.eval (c i)‖ ≤ b*r := by
  have hpos : 0 < ∏ j ∈ s.erase i, d j := Finset.prod_pos hd
  have hprod : (∏ j ∈ s.erase i, d j) ≤
      ∏ j ∈ s.erase i, ‖c i-c j‖ :=
    Finset.prod_le_prod₀ (fun j hj => (hd j hj).le) hsep
  have hw : ‖Lagrange.nodalWeight s c i‖ ≤ (∏ j ∈ s.erase i, d j)⁻¹ := by
    rw [Lagrange.nodalWeight, norm_prod]
    simp only [norm_inv]
    rw [Finset.prod_inv_distrib]
    exact inv_anti₀ hpos hprod
  rw [norm_mul]
  calc
    ‖Lagrange.nodalWeight s c i‖*‖P.eval (c i)‖ ≤
        (∏ j ∈ s.erase i, d j)⁻¹*‖P.eval (c i)‖ :=
      mul_le_mul_of_nonneg_right hw (norm_nonneg _)
    _ ≤ (∏ j ∈ s.erase i, d j)⁻¹*(b*r*∏ j ∈ s.erase i, d j) :=
      mul_le_mul_of_nonneg_left heval (inv_nonneg.mpr hpos.le)
    _ = b*r := by field_simp

/-- A root cover certified using rational coordinate separations and residual
bounds. The finite arithmetic certificates can be checked independently per node. -/
theorem monic_root_cover_of_separations {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c : ι → ℂ) (r b : ι → ℝ) (d : ι → ι → ℝ) (P : ℂ[X])
    (hc : Set.InjOn c s) (hP : P.Monic) (hdegree : P.degree = (s.card : WithBot ℕ))
    (hr : ∀ i ∈ s, 0 < r i)
    (hd : ∀ i ∈ s, ∀ j ∈ s.erase i, 0 < d i j)
    (hsep : ∀ i ∈ s, ∀ j ∈ s.erase i, d i j ≤ ‖c i-c j‖)
    (heval : ∀ i ∈ s, |(P.eval (c i)).re|+|(P.eval (c i)).im| ≤
      b i*r i*∏ j ∈ s.erase i, d i j)
    (hsmall : ∑ i ∈ s, b i < 1)
    (z : ℂ) (hz : P.eval z=0) :
    ∃ i ∈ s, ‖z-c i‖ < r i := by
  apply monic_root_cover s c r P hc hP hdegree hr _ z hz
  apply lt_of_le_of_lt _ hsmall
  apply Finset.sum_le_sum
  intro i hi
  apply (div_le_iff₀ (hr i hi)).mpr
  exact nodal_eval_bound_of_separations s c P i (d i) (b i) (r i)
    (hd i hi) (hsep i hi) ((Complex.norm_le_abs_re_add_abs_im _).trans (heval i hi))

#print axioms nodal_eval_bound_of_separations
#print axioms monic_root_cover_of_separations
end QuantitativeArithmeticPolynomialRootCover
end
end
