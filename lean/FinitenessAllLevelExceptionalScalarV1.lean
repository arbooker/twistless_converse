module

public import FinitenessAllLevelSeparableCertificateV1
public import FinitenessAllLevelGenericSeparableV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelCoefficientRing

open Complex Set MvPolynomial Filter
open scoped Topology

variable {ι σ : Type*} {U : Set ℂ} (g : ι → ℂ → ℂ)

/-- One nonzero element of the analytic coefficient ring controls all
coordinate separabilities, on the entire domain. -/
theorem exceptional_scalar [Countable ι] [Finite σ]
    (hU : IsOpen U) (hconn : IsPreconnected U) (hne : U.Nonempty)
    (hg : ∀ j, AnalyticOnNhd ℂ (g j) U)
    (I : Ideal (MvPolynomial σ (ring U g)))
    (hf : ∀ z : U, (zeroLocus ℂ (I.map (MvPolynomial.map (evaluation U g z)))).Finite) :
    ∃ a : ring U g, a ≠ 0 ∧ ∀ i : σ, ∃ q : Polynomial (ring U g),
      q ≠ 0 ∧
      (∀ z : U, evaluation U g z a ≠ 0 → (q.map (evaluation U g z)).Separable) ∧
      ∀ z : U, ∀ v ∈ zeroLocus ℂ (I.map (MvPolynomial.map (evaluation U g z))),
        q.eval₂ (evaluation U g z) (v i) = 0 := by
  classical
  let := Fintype.ofFinite σ
  obtain ⟨w, _, hw⟩ := exists_injective_evaluation U g hconn hg hU (Subset.refl U) hne
  let := Function.Injective.isDomain (evaluation U g w) hw
  let : CharZero (ring U g) := ⟨fun a b h => by
    have he := congrArg (evaluation U g w) h
    simpa only [map_natCast, Nat.cast_inj] using he⟩
  have hdata (i : σ) : ∃ q : Polynomial (ring U g), q ≠ 0 ∧
      Polynomial.aeval (X i) q ∈ I.radical ∧
      ∃ a : ring U g, a ≠ 0 ∧ ∃ u v : Polynomial (ring U g),
        u * q + v * q.derivative = Polynomial.C a := by
    obtain ⟨q, hq, hs, hi⟩ := FinitenessAllLevelFiniteFiberAlgebra.separable_coordinate_eliminant
      (evaluation U g w) hw I (hf w) i
    exact ⟨q, hq, hi, FinitenessAllLevelFiniteFiberAlgebra.separable_certificate
      (evaluation U g w) hw q hs⟩
  choose q hq hi a ha u v hcert using hdata
  refine ⟨∏ i, a i, Finset.prod_ne_zero_iff.mpr (fun i _ => ha i), fun i =>
    ⟨q i, hq i, ?_, fun z v hv => eval_radical_eliminant g I (q i) i (hi i) z v hv⟩⟩
  intro z hz
  apply FinitenessAllLevelFiniteFiberAlgebra.separable_of_certificate
    (q i) (a i) (u i) (v i) (hcert i) (evaluation U g z)
  rw [map_prod] at hz
  exact Finset.prod_ne_zero_iff.mp hz i (Finset.mem_univ i)

/-- The exception function is nonzero on a punctured neighborhood of EVERY
point, including its own zeros. No generic-parameter assumption remains. -/
theorem representative_nonzero_punctured (hconn : IsPreconnected U)
    (hg : ∀ j, AnalyticOnNhd ℂ (g j) U)
    {a : ring U g} (ha : a ≠ 0) {w : ℂ} (hw : w ∈ U) :
    ∀ᶠ z in 𝓝[≠] w, representative U g a z ≠ 0 := by
  have han := representative_analytic U g hg a
  rcases (han w hw).eventually_eq_zero_or_eventually_ne_zero with hz | hz
  · exact False.elim ((representative_not_identically_zero g a ha)
      (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hw hz))
  · exact hz

#print axioms exceptional_scalar
#print axioms representative_nonzero_punctured

end FinitenessAllLevelCoefficientRing
