module

public import QuantitativeSpectralLogDerivativeV1
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
@[expose] public section

namespace QuantitativeSpectralTriangularLog

variable {𝔄 : Type*} [CStarAlgebra 𝔄]

/-- The logarithmic derivative of a Gram path reduces to twice the real
trace of the original logarithmic derivative. This is an algebraic consequence
of cyclicity and compatibility with the adjoint. -/
theorem trace_gram_inverse_derivative (L V : 𝔄) (hu : IsUnit L)
    (τ : 𝔄 →L[ℝ] ℝ) (hcyc : ∀ B C, τ (B*C) = τ (C*B))
    (hstar : ∀ B, τ (star B) = τ B) :
    τ (Ring.inverse (star L*L)*(star V*L+star L*V)) =
      2*τ (Ring.inverse L*V) := by
  let C := Ring.inverse L
  have hc : C*L = 1 := Ring.inverse_mul_cancel L hu
  have hl : L*C = 1 := Ring.mul_inverse_cancel L hu
  have hsc : star C*star L = 1 := by
    rw [← star_mul, hl, star_one]
  rw [Ring.inverse_mul (Or.inr hu), Ring.inverse_star, mul_add, map_add]
  change τ (C*star C*(star V*L))+τ (C*star C*(star L*V)) = 2*τ (C*V)
  have hfirst : τ (C*star C*(star V*L)) = τ (C*V) := by
    rw [← mul_assoc (C*star C) (star V) L, hcyc _ L]
    rw [← mul_assoc L (C*star C) (star V), ← mul_assoc L C (star C), hl, one_mul]
    rw [← star_mul, hstar, hcyc V C]
  have hsecond : C*star C*(star L*V) = C*V := by
    rw [mul_assoc, ← mul_assoc (star C) (star L) V, hsc, one_mul]
  rw [hfirst, hsecond]
  ring

/-- The inverse of a unipotent perturbation is its finite geometric sum;
this is an actual inverse identity, with no determinant convention. -/
theorem nilpotent_inverse (V : 𝔄) {n : ℕ} (hn : V^n = 0) (t : ℝ) :
    Ring.inverse (1+t • V) = ∑ i ∈ Finset.range n, (-t)^i • V^i := by
  let X := (-t) • V
  have hX : X^n = 0 := by
    dsimp [X]
    rw [smul_pow, hn, smul_zero]
  have hu : IsUnit (1-X) := (show IsNilpotent X from ⟨n,hX⟩).isUnit_one_sub
  have hp : (1-X)*(∑ i ∈ Finset.range n, X^i) = 1 := by
    rw [← neg_sub X 1, neg_mul, mul_geom_sum, hX]
    simp
  have hi : Ring.inverse (1-X) = ∑ i ∈ Finset.range n, X^i := by
    calc
      Ring.inverse (1-X) = Ring.inverse (1-X)*1 := (mul_one _).symm
      _ = Ring.inverse (1-X)*((1-X)*(∑ i ∈ Finset.range n, X^i)) := by rw [hp]
      _ = ∑ i ∈ Finset.range n, X^i := Ring.inverse_mul_cancel_left _ _ hu
  dsimp [X] at hi
  simp only [smul_pow] at hi
  simpa only [neg_smul, sub_neg_eq_add] using hi

/-- Vanishing positive power traces imply the exact zero logarithmic
resolvent trace along a unipotent path. Strict triangular block matrices
supply the power-trace hypothesis. -/
theorem trace_nilpotent_resolvent (V : 𝔄) {n : ℕ} (hn : V^n = 0)
    (τ : 𝔄 →L[ℝ] ℝ) (hp : ∀ j : ℕ, 0 < j → τ (V^j) = 0) (t : ℝ) :
    τ (Ring.inverse (1+t • V)*V) = 0 := by
  rw [nilpotent_inverse V hn t, Finset.sum_mul, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [smul_mul_assoc, ← pow_succ, map_smul, hp (i+1) (Nat.succ_pos i), smul_zero]

/-- A unipotent element has zero real tracial logarithmic Gram determinant.
The logarithm is the actual continuous-functional-calculus logarithm, and
its constancy is proved by differentiation along the unipotent path. -/
theorem trace_log_unipotent_gram (V : 𝔄) {n : ℕ} (hn : V^n = 0)
    (τ : 𝔄 →L[ℝ] ℝ) (hcyc : ∀ B C, τ (B*C) = τ (C*B))
    (hstar : ∀ B, τ (star B) = τ B)
    (hp : ∀ j : ℕ, 0 < j → τ (V^j) = 0) (t : ℝ) :
    τ (CFC.log (star (1+t • V)*(1+t • V))) = 0 := by
  let L : ℝ → 𝔄 := fun x => 1+x • V
  let G : ℝ → 𝔄 := fun x => star (L x)*L x
  let G' : ℝ → 𝔄 := fun x => star V*L x+star (L x)*V
  have hL (x : ℝ) : HasDerivAt L V x := by
    simpa [L] using ((hasDerivAt_id x).smul_const V).const_add 1
  have hu (x : ℝ) : IsUnit (L x) :=
    (show IsNilpotent V from ⟨n,hn⟩).smul x |>.isUnit_one_add
  have hG (x : ℝ) : HasDerivAt G (G' x) x := (hL x).star.mul (hL x)
  have hG' : Continuous G' := by dsimp [G',L]; fun_prop
  have hself (x : ℝ) : IsSelfAdjoint (G x) := IsSelfAdjoint.star_mul_self (L x)
  have hpos (x : ℝ) : ∀ r ∈ spectrum ℝ (G x), 0 < r := by
    intro r hr
    have hnonneg : 0 ≤ r := spectrum_star_mul_self_nonneg r hr
    have hnzero : r ≠ 0 := by
      intro he
      subst r
      exact spectrum.zero_notMem (R := ℝ) ((hu x).star.mul (hu x)) hr
    exact lt_of_le_of_ne hnonneg hnzero.symm
  have hd (x : ℝ) : HasDerivAt (fun y => τ (CFC.log (G y))) 0 x := by
    have hh := QuantitativeSpectralLogDerivative.hasDerivAt_trace_log_of_continuous
      hG hG' hself hpos τ hcyc x
    have hz : τ (Ring.inverse (G x)*G' x) = 0 := by
      dsimp [G,G']
      rw [trace_gram_inverse_derivative (L x) V (hu x) τ hcyc hstar]
      rw [show L x = 1+x • V from rfl, trace_nilpotent_resolvent V hn τ hp x, mul_zero]
    rwa [hz] at hh
  have he := is_const_of_deriv_eq_zero
    (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) t 0
  simpa [G,L] using he

/-- Congruence by a unipotent preserves the actual tracial Gram logarithm
of any fixed invertible factor. This is the form needed after separating
the diagonal part of a finite triangular deflation operator. -/
theorem trace_log_unipotent_congruence (B V : 𝔄) (hB : IsUnit B) {n : ℕ} (hn : V^n = 0)
    (τ : 𝔄 →L[ℝ] ℝ) (hcyc : ∀ B C, τ (B*C) = τ (C*B))
    (hstar : ∀ B, τ (star B) = τ B)
    (hp : ∀ j : ℕ, 0 < j → τ (V^j) = 0) (t : ℝ) :
    τ (CFC.log (star (B*(1+t • V))*(B*(1+t • V)))) =
      τ (CFC.log (star B*B)) := by
  let L : ℝ → 𝔄 := fun x => B*(1+x • V)
  let G : ℝ → 𝔄 := fun x => star (L x)*L x
  let G' : ℝ → 𝔄 := fun x => star (B*V)*L x+star (L x)*(B*V)
  have hL (x : ℝ) : HasDerivAt L (B*V) x := by
    simpa [L] using (((hasDerivAt_id x).smul_const V).const_add 1).const_mul B
  have hu (x : ℝ) : IsUnit (L x) :=
    hB.mul ((show IsNilpotent V from ⟨n,hn⟩).smul x |>.isUnit_one_add)
  have hG (x : ℝ) : HasDerivAt G (G' x) x := (hL x).star.mul (hL x)
  have hG' : Continuous G' := by dsimp [G',L]; fun_prop
  have hself (x : ℝ) : IsSelfAdjoint (G x) := IsSelfAdjoint.star_mul_self (L x)
  have hpos (x : ℝ) : ∀ r ∈ spectrum ℝ (G x), 0 < r := by
    intro r hr
    have hnonneg : 0 ≤ r := spectrum_star_mul_self_nonneg r hr
    have hnzero : r ≠ 0 := by
      intro he
      subst r
      exact spectrum.zero_notMem (R := ℝ) ((hu x).star.mul (hu x)) hr
    exact lt_of_le_of_ne hnonneg hnzero.symm
  have hd (x : ℝ) : HasDerivAt (fun y => τ (CFC.log (G y))) 0 x := by
    have hh := QuantitativeSpectralLogDerivative.hasDerivAt_trace_log_of_continuous
      hG hG' hself hpos τ hcyc x
    have hz : τ (Ring.inverse (G x)*G' x) = 0 := by
      dsimp [G,G']
      rw [trace_gram_inverse_derivative (L x) (B*V) (hu x) τ hcyc hstar]
      have he : Ring.inverse (L x)*(B*V) = Ring.inverse (1+x • V)*V := by
        dsimp [L]
        rw [Ring.inverse_mul (Or.inl hB), mul_assoc,
          ← mul_assoc (Ring.inverse B) B V, Ring.inverse_mul_cancel B hB, one_mul]
      rw [he, trace_nilpotent_resolvent V hn τ hp x, mul_zero]
    rwa [hz] at hh
  have he := is_const_of_deriv_eq_zero
    (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) t 0
  simpa [G,L] using he

#print axioms trace_gram_inverse_derivative
#print axioms trace_log_unipotent_gram
#print axioms trace_log_unipotent_congruence
#print axioms nilpotent_inverse
#print axioms trace_nilpotent_resolvent

end QuantitativeSpectralTriangularLog
