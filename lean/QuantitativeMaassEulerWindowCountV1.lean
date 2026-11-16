module

public import QuantitativeMaassEulerHilbertIndependentV1
public import QuantitativeMaassEigenfamilyFiniteV1
public import QuantitativeConcreteGoalsV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeMaass

open QuantitativeConcreteGoals

variable {N Q : ℕ} {hQ : 0<Q} (hN : 0<N)
  (A : FinitenessCertificate.Certificate N Q hQ) (P : FinitenessGlobalHeight.Parameters A)

/-- The literal window remembers both the parameter and coefficients. -/
def originalWindowClass (σ : ℕ) (t ε : ℝ) (p : maassWindow N σ t ε) :
    AsymptoticHyperbolicSlash.Space :=
  principalEulerWeightedLp hN A P p.val.1 σ p.property.2.2

theorem originalWindowClass_independent (σ : ℕ) (t ε : ℝ) :
    LinearIndependent ℂ (originalWindowClass hN A P σ t ε) := by
  let f : maassWindow N σ t ε →
      Σ r : {r : ℝ // 0≤r},MaassOriginal.EulerS N (.principal r.val) σ :=
    fun p => ⟨⟨p.val.1,p.property.1⟩,⟨p.val.2,p.property.2.2⟩⟩
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    exact congrArg (fun rb => (rb.1.val,rb.2.val)) hpq
  exact (originalEuler_weighted_classes_independent hN A P σ).comp f hf

/-- Conditional counting interface for the literal original Euler window.
The spectral action and Hilbert--Schmidt majorant are explicit remaining
analytic inputs; this theorem does not assert that they exist. Finiteness is
proved independently of the convention that ncard vanishes on infinite sets. -/
theorem originalWindow_count_of_spectral_majorant {ι : Type*}
    (σ : ℕ) (t ε : ℝ)
    (basis : HilbertBasis ι ℂ AsymptoticHyperbolicSlash.Space)
    (B : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)
    (h : ℝ → ℝ)
    (heigen : ∀ p : maassWindow N σ t ε,
      B (originalWindowClass hN A P σ t ε p)=
        (h p.val.1 : ℂ) • originalWindowClass hN A P σ t ε p)
    (hlower : ∀ r ∈ Set.Icc t (t+ε), 1≤h r)
    (hB : Summable (fun i => ‖B (basis i)‖^2)) :
    (maassWindow N σ t ε).Finite ∧
      ((maassWindow N σ t ε).ncard : ℝ) ≤ hilbertSchmidtEnergy basis B := by
  obtain ⟨hf,hbound⟩ := independent_eigenfamily_finite basis B
    (originalWindowClass hN A P σ t ε) (originalWindowClass_independent hN A P σ t ε)
    (fun p => h p.val.1) heigen (fun p => hlower p.val.1 p.property.2.1) hB
  let := hf
  refine ⟨Set.toFinite _,?_⟩
  simpa only [Nat.card_coe_set_eq] using hbound

#print axioms originalWindowClass
#print axioms originalWindowClass_independent
#print axioms originalWindow_count_of_spectral_majorant

end QuantitativeMaass
