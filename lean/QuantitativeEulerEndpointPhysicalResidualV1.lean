module

public import QuantitativeEulerEndpointCornerResidualV1
public import QuantitativeEulerEndpointPhysicalIterationV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPhysicalCorner
open Polynomial QuantitativeEulerEndpointUpdateExpression QuantitativeEulerEndpointResidual
open QuantitativeEulerEndpointBernstein
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Quantitative invariance of the actual sharpened band update; residuals
of the previous filter and the original normalized Gram are allowed. -/
theorem sharpened_residual (P a g E : A) (hP : IsStarProjection P) (hP0 : 0≤P) (hP1 : P≤1)
    (hal : P*a=a) (har : a*P=a) (hgl : P*g=g) (hgr : g*P=g)
    (ha0 : 0≤a) (ha1 : a≤1) (hg0 : 0≤g) (hg1 : g≤1) (hPE : P*E=E)
    (n : ℕ) (q : ℝ[X]) (hq : q.eval 1=1) :
    ‖(aeval (cornerUpdate P a g n) q*P)*E-E‖≤
      slopeMass q*((3+(n:ℝ))*‖a*E-E‖+(n:ℝ)*‖g*E‖) := by
  have hD := compressed_complement_order P hP a g hal har hgl hgr ha0 ha1 hg0 hg1
  have hu := corner_update_order P hP a g hal har hgl hgr ha0 ha1 hg0 hg1 n
  have hn (b : A) (hb0 : 0≤b) (hb1 : b≤1) : ‖b‖≤1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg b hb0).mpr hb1
  rw [mul_assoc,hPE]
  exact (polynomial_fixed_residual _ E (hn _ hu.1 (hu.2.trans ha1)) q hq).trans
    (mul_le_mul_of_nonneg_left
      (corner_update_residual P a g E (hn P hP0 hP1) (hn a ha0 ha1) (hn g hg0 hg1)
        (hn _ hD.1 (hD.2.trans hP1)) hPE n) (slopeMass_nonneg q))

#print axioms sharpened_residual
end QuantitativeEulerEndpointPhysicalCorner
namespace QuantitativeEulerEndpointResidual
open Polynomial

/-- An explicit majorant for accumulated approximate-solution error. -/
def errorBudget (L : ℕ → ℕ) (q : ℕ → ℝ[X]) : ℕ → ℝ
  | 0 => 1
  | n+1 => (1+slopeMass (q n))*(4+2*(L n:ℝ))*errorBudget L q n

theorem errorBudget_ge_one (L : ℕ → ℕ) (q : ℕ → ℝ[X]) (n : ℕ) : 1≤errorBudget L q n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hs := slopeMass_nonneg (q n)
    have hL : (0:ℝ)≤L n := Nat.cast_nonneg _
    have hf : 1≤(1+slopeMass (q n))*(4+2*(L n:ℝ)) := by nlinarith
    dsimp only [errorBudget]
    nlinarith

theorem errorBudget_step (L : ℕ → ℕ) (q : ℕ → ℝ[X]) (n : ℕ) {δ r s : ℝ}
    (hδ : 0≤δ) (hr : r≤errorBudget L q n*δ) (hs : s≤δ) :
    slopeMass (q n)*((3+(L n:ℝ))*r+(L n:ℝ)*s)≤errorBudget L q (n+1)*δ := by
  have hb := errorBudget_ge_one L q n
  have hq := slopeMass_nonneg (q n)
  have hL : (0:ℝ)≤L n := Nat.cast_nonneg _
  have hh := mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left hr (by positivity : 0≤3+(L n:ℝ)))
    (mul_le_mul_of_nonneg_left hs hL)) hq
  have hbig : slopeMass (q n)*((3+(L n:ℝ))*errorBudget L q n+(L n:ℝ))≤
      (1+slopeMass (q n))*(4+2*(L n:ℝ))*errorBudget L q n := by
    have hb0 : 0≤errorBudget L q n := by linarith
    nlinarith [mul_nonneg hq (mul_nonneg hL (sub_nonneg.mpr hb)),
      mul_nonneg hq hb0,mul_nonneg hL hb0]
  have hfinal := mul_le_mul_of_nonneg_right hbig hδ
  dsimp only [errorBudget]
  nlinarith

#print axioms errorBudget_step
end QuantitativeEulerEndpointResidual
namespace QuantitativeEulerEndpointNestedExpression
open AsymptoticFiniteBranch QuantitativeHolomorphic Polynomial
open QuantitativeEulerEndpointBandExpression QuantitativeEulerEndpointBernstein QuantitativeEulerEndpointResidual

/-- The SAME finite physical filter approximately fixes every band-supported
operator with bounded initial and original Gram residuals. -/
theorem physical_iteration_residual (ε H : ℝ) (initial : Expression) (g : ℕ → Expression)
    (L : ℕ → ℕ) (q : ℕ → ℝ[X]) (n m : ℕ)
    (E : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)
    (hPE : holomorphicSum (unitExpression ε H) m*E=E)
    (hi : let P := holomorphicSum (unitExpression ε H) m
      let A := holomorphicSum initial m
      0≤A ∧ A≤P ∧ P*A=A ∧ A*P=A)
    (hg : ∀ j<n,let P := holomorphicSum (unitExpression ε H) m
      let G := holomorphicSum (g j) m
      0≤G ∧ G≤1 ∧ P*G=G ∧ G*P=G)
    (hq : ∀ j<n,ScalarSharpening (q j))
    {δ : ℝ} (hδ : 0≤δ) (hiE : ‖holomorphicSum initial m*E-E‖≤δ)
    (hgE : ∀ j<n,‖holomorphicSum (g j) m*E‖≤δ) :
    ‖holomorphicSum (expression (unitExpression ε H) initial g L q n) m*E-E‖≤
      errorBudget L q n*δ := by
  induction n with
  | zero => simpa only [expression,errorBudget,one_mul] using hiE
  | succ n ih =>
    have hgn := hg n (by omega)
    have ho := physical_iteration_order ε H initial g L q n m hi
      (fun j hj => hg j (by omega)) (fun j hj => hq j (by omega))
    have hP := QuantitativeEulerEndpointPhysicalGram.unit_order ε H m
    have herr := ih (fun j hj => hg j (by omega)) (fun j hj => hq j (by omega))
      (fun j hj => hgE j (by omega))
    rw [expression,holomorphic_sharpened]
    exact (QuantitativeEulerEndpointPhysicalCorner.sharpened_residual _ _ _ E
      (QuantitativeEulerEndpointPhysicalGram.unit_isStarProjection ε H m) hP.1 hP.2
      ho.2.2.2.1 ho.2.2.2.2 hgn.2.2.1 hgn.2.2.2 ho.1 (ho.2.2.1.trans hP.2)
      hgn.1 hgn.2.1 hPE (L n) (q n) (hq n (by omega)).2.1).trans
      (errorBudget_step L q n hδ herr (hgE n (by omega)))

#print axioms physical_iteration_residual
end QuantitativeEulerEndpointNestedExpression
