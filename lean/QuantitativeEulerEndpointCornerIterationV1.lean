module

public import QuantitativeEulerEndpointPhysicalCornerV1
public import QuantitativeEulerEndpointCornerAmbientV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointCornerIteration
open Polynomial QuantitativeEulerEndpointBernstein QuantitativeEulerEndpointUpdateExpression
variable {𝔄 : Type*} [CStarAlgebra 𝔄] [PartialOrder 𝔄] [StarOrderedRing 𝔄]

/-- A finite horizon of corner updates preserves positivity and the entire
source projection, and decreases the initial filter. -/
theorem order (P : 𝔄) (hP : IsStarProjection P) (hP1 : P≤1)
    (F G : ℕ → 𝔄) (L : ℕ → ℕ) (q : ℕ → ℝ[X]) (n : ℕ)
    (hi : 0≤F 0 ∧ F 0≤P ∧ P*F 0=F 0 ∧ F 0*P=F 0)
    (hg : ∀ j<n,0≤G j ∧ G j≤1 ∧ P*G j=G j ∧ G j*P=G j)
    (hq : ∀ j<n,ScalarSharpening (q j))
    (hrec : ∀ j<n,F (j+1)=aeval (cornerUpdate P (F j) (G j) (L j)) (q j)*P) :
    0≤F n ∧ F n≤F 0 ∧ F n≤P ∧ P*F n=F n ∧ F n*P=F n := by
  induction n with
  | zero => exact ⟨hi.1,le_rfl,hi.2⟩
  | succ n ih =>
    have hp := ih (fun j hj => hg j (by omega)) (fun j hj => hq j (by omega))
      (fun j hj => hrec j (by omega))
    have hn := hg n (by omega)
    have hs := QuantitativeEulerEndpointPhysicalCorner.sharpened_order P hP (F n) (G n)
      hp.2.2.2.1 hp.2.2.2.2 hn.2.2.1 hn.2.2.2 hp.1 (hp.2.2.1.trans hP1)
      hn.1 hn.2.1 (L n) (hq n (by omega))
    rw [hrec n (by omega)]
    exact ⟨hs.1,hs.2.1.trans hp.2.1,hs.2.1.trans hp.2.2.1,hs.2.2⟩

omit [PartialOrder 𝔄] [StarOrderedRing 𝔄] in
/-- The same supported recursion obeys the ambient formula used in the
operator perturbation estimate. -/
theorem ambient_step (P : 𝔄) (hP : IsStarProjection P) (a g : 𝔄)
    (hl : P*a=a) (hr : a*P=a) (d : ℕ) (q : ℝ[X]) (hq : q.eval 0=0) :
    aeval (cornerUpdate P a g d) q*P=
      aeval (QuantitativeEulerEndpointSoftUpdate.update a (a*g*a) d) q :=
  QuantitativeEulerEndpointCornerAmbient.corner_sharpened_eq P a g hP.isIdempotentElem.eq hl hr d q hq

#print axioms order
#print axioms ambient_step
end QuantitativeEulerEndpointCornerIteration
