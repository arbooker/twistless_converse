module

public import QuantitativeEulerEndpointTerminalUnitExpressionV1
public import QuantitativeEulerEndpointCornerIterationV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointTerminalExpression
open FinitenessCertificate FinitenessGlobalHeight AsymptoticFiniteBranch QuantitativeHolomorphic Polynomial
open QuantitativeEulerEndpointNestedExpression QuantitativeEulerEndpointBernstein
open QuantitativeEulerEndpointUpdateExpression QuantitativeEulerEndpointBandExpression
open QuantitativeEulerEndpointPolynomialExpression
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

def iterate (g : ℕ → Expression) (L : ℕ → ℕ) (q : ℕ → ℝ[X]) (n : ℕ) : Expression :=
  expression (unit A P) (unit A P) g L q n

theorem regular_step (g : ℕ → Expression) (L : ℕ → ℕ) (q : ℕ → ℝ[X]) (j : ℕ)
    (x : UpperHalfPlane) :
    regularSum (iterate A P g L q (j+1)) x=
      aeval (cornerUpdate (regularSum (unit A P) x)
        (regularSum (iterate A P g L q j) x) (regularSum (g j) x) (L j)) (q j)*
          regularSum (unit A P) x := by
  unfold iterate
  rw [expression,sharpenedExpression,regular_cornerPolynomial,regular_update]

theorem physical_step (g : ℕ → Expression) (L : ℕ → ℕ) (q : ℕ → ℝ[X]) (j m : ℕ) :
    holomorphicSum (iterate A P g L q (j+1)) m=
      aeval (cornerUpdate (holomorphicSum (unit A P) m)
        (holomorphicSum (iterate A P g L q j) m) (holomorphicSum (g j) m) (L j)) (q j)*
          holomorphicSum (unit A P) m := by
  unfold iterate
  rw [expression,holomorphic_sharpened]

/-- Positivity, contraction and support on the whole regular terminal strip. -/
theorem regular_order (g : ℕ → Expression) (L : ℕ → ℕ) (q : ℕ → ℝ[X]) (n : ℕ)
    (x : UpperHalfPlane)
    (hg : ∀ j<n,let U := regularSum (unit A P) x
      let G := regularSum (g j) x
      0≤G ∧ G≤1 ∧ U*G=G ∧ G*U=G)
    (hq : ∀ j<n,ScalarSharpening (q j)) :
    let U := regularSum (unit A P) x
    let F := regularSum (iterate A P g L q n) x
    0≤F ∧ F≤1 ∧ F≤U ∧ U*F=F ∧ F*U=F := by
  have hp := unit_regular_projection A P x
  have hu := unit_regular_order A P x
  have hi : let F := regularSum (iterate A P g L q 0) x
      let U := regularSum (unit A P) x
      0≤F ∧ F≤U ∧ U*F=F ∧ F*U=F :=
    ⟨hu.1,le_rfl,hp.isIdempotentElem.eq,hp.isIdempotentElem.eq⟩
  have h := QuantitativeEulerEndpointCornerIteration.order _ hp hu.2
    (fun j => regularSum (iterate A P g L q j) x) (fun j => regularSum (g j) x)
    L q n hi hg hq (fun j _ => regular_step A P g L q j x)
  exact ⟨h.1,h.2.2.1.trans hu.2,h.2.2⟩

/-- The identical finite expression is positive and contracting in the
physical representation; no truncation of the terminal source is used. -/
theorem physical_order (g : ℕ → Expression) (L : ℕ → ℕ) (q : ℕ → ℝ[X]) (n m : ℕ)
    (hg : ∀ j<n,let U := holomorphicSum (unit A P) m
      let G := holomorphicSum (g j) m
      0≤G ∧ G≤1 ∧ U*G=G ∧ G*U=G)
    (hq : ∀ j<n,ScalarSharpening (q j)) :
    let U := holomorphicSum (unit A P) m
    let F := holomorphicSum (iterate A P g L q n) m
    0≤F ∧ F≤1 ∧ F≤U ∧ U*F=F ∧ F*U=F := by
  have hp := unit_physical_projection A P m
  have hu := unit_physical_order A P m
  have hi : let F := holomorphicSum (iterate A P g L q 0) m
      let U := holomorphicSum (unit A P) m
      0≤F ∧ F≤U ∧ U*F=F ∧ F*U=F :=
    ⟨hu.1,le_rfl,hp.isIdempotentElem.eq,hp.isIdempotentElem.eq⟩
  have h := QuantitativeEulerEndpointCornerIteration.order _ hp hu.2
    (fun j => holomorphicSum (iterate A P g L q j) m) (fun j => holomorphicSum (g j) m)
    L q n hi hg hq (fun j _ => physical_step A P g L q j m)
  exact ⟨h.1,h.2.2.1.trans hu.2,h.2.2⟩

theorem regular_ambient_step (g : ℕ → Expression) (L : ℕ → ℕ) (q : ℕ → ℝ[X])
    (j : ℕ) (x : UpperHalfPlane)
    (hg : ∀ i<j,let U := regularSum (unit A P) x
      let G := regularSum (g i) x
      0≤G ∧ G≤1 ∧ U*G=G ∧ G*U=G)
    (hq : ∀ i<j+1,ScalarSharpening (q i)) :
    let F := regularSum (iterate A P g L q j) x
    regularSum (iterate A P g L q (j+1)) x=
      aeval (QuantitativeEulerEndpointSoftUpdate.update F (F*regularSum (g j) x*F) (L j)) (q j) := by
  have ho := regular_order A P g L q j x hg (fun i hi => hq i (by omega))
  rw [regular_step]
  exact QuantitativeEulerEndpointCornerIteration.ambient_step _ (unit_regular_projection A P x)
    _ _ ho.2.2.2.1 ho.2.2.2.2 (L j) (q j) (hq j (by omega)).1

#print axioms regular_order
#print axioms physical_order
#print axioms regular_ambient_step
end QuantitativeEulerEndpointTerminalExpression
