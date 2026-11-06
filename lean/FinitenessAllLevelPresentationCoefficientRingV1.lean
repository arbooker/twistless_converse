module

public import FinitenessAllLevelAnalyticEliminantV1
public import FinitenessAllLevelPolynomialPresentationV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelCoefficientRing

open MvPolynomial

def generator {ι : Type*} (U : Set ℂ) (g : ι → ℂ → ℂ) (i : ι) : ring U g :=
  ⟨fun z => g i z, ⟨X i, by ext z; simp⟩⟩

@[simp] theorem evaluation_generator {ι : Type*} (U : Set ℂ) (g : ι → ℂ → ℂ)
    (z : U) (i : ι) : evaluation U g z (generator U g i) = g i z := rfl

end FinitenessAllLevelCoefficientRing

namespace FinitenessAllLevelPolynomialPresentation

open Complex Set FinitenessAllLevelQuadraticCoordinates FinitenessAllLevelCoefficientRing

abbrev Entry (n : ℕ) := Unit ⊕ (Fin n ⊕ (Fin n × Fin n))

def entry {n : ℕ} (e : Entry n) : Coeff n →ₗ[ℂ] ℂ where
  toFun c := match e with
    | .inl _ => c.1
    | .inr (.inl i) => c.2.1 i
    | .inr (.inr (i, j)) => c.2.2 i j
  map_add' c d := by cases e with | inl _ => rfl | inr v => cases v <;> rfl
  map_smul' a c := by cases e with | inl _ => rfl | inr v => cases v <;> rfl

variable {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  {R : ℂ → X → Prop}

def Presentation.coefficientFunctions (c : Presentation ι R) : (ι × Entry c.n) → ℂ → ℂ :=
  fun j z => entry j.2 (c.coefficients j.1 z)

theorem Presentation.coefficientFunctions_analytic (c : Presentation ι R) (j : ι × Entry c.n) :
    AnalyticOnNhd ℂ (c.coefficientFunctions j) c.U := by
  intro z hz
  exact ((entry j.2).toContinuousLinearMap.analyticAt _).comp (c.analytic_coefficients j.1 z hz)

/-- The actual finite equations over the ring of their holomorphic
coefficient functions. Specialization is proved to recover the original
polynomials exactly. -/
def Presentation.ringEquation (c : Presentation ι R) (j : ι) :
    MvPolynomial (Fin c.n) (ring c.U c.coefficientFunctions) :=
  MvPolynomial.C (generator c.U c.coefficientFunctions (j, .inl ())) +
    ∑ i, MvPolynomial.C (generator c.U c.coefficientFunctions (j, .inr (.inl i))) *
      MvPolynomial.X i +
    ∑ i, ∑ k, MvPolynomial.C (generator c.U c.coefficientFunctions (j, .inr (.inr (i, k)))) *
      MvPolynomial.X i * MvPolynomial.X k

theorem Presentation.map_ringEquation (c : Presentation ι R) (z : c.U) (j : ι) :
    MvPolynomial.map (evaluation c.U c.coefficientFunctions z) (c.ringEquation j) =
      polynomial (c.coefficients j z) := by
  simp [ringEquation, polynomial, coefficientFunctions, entry]

def Presentation.ringIdeal (c : Presentation ι R) :
    Ideal (MvPolynomial (Fin c.n) (ring c.U c.coefficientFunctions)) :=
  Ideal.span (range c.ringEquation)

theorem Presentation.map_ringIdeal (c : Presentation ι R) (z : c.U) :
    c.ringIdeal.map (MvPolynomial.map (evaluation c.U c.coefficientFunctions z)) =
      c.fiberIdeal z := by
  rw [ringIdeal, Ideal.map_span, ← Set.range_comp]
  simp only [Function.comp_def, c.map_ringEquation, Presentation.fiberIdeal]

theorem Presentation.zeroLocus_finite (c : Presentation ι R) {z : ℂ}
    (hz : z ∈ c.U) (hf : {t : ℂ × X | R t.1 t.2 ∧ t.1 = z}.Finite) :
    (MvPolynomial.zeroLocus ℂ (c.fiberIdeal z)).Finite := by
  have hinj : Function.Injective (fun v : Fin c.n → ℂ => (z, c.lift z v)) :=
    fun _ _ he => c.injective_lift z (congrArg Prod.snd he)
  apply (Set.Finite.preimage hinj.injOn hf).subset
  intro v hv
  exact ⟨(c.exact_locus z hz _).mpr ⟨v, (c.mem_zeroLocus z v).mp hv, rfl⟩, rfl⟩

/-- Actual chart coordinates satisfy one analytic-family eliminant on the
whole connected chart, rather than a different polynomial at each fiber. -/
theorem Presentation.coordinate_eliminant [Countable ι] (c : Presentation ι R)
    (hconn : IsPreconnected c.U) (hne : c.U.Nonempty)
    (hf : ∀ z : ℂ, {t : ℂ × X | R t.1 t.2 ∧ t.1 = z}.Finite) (i : Fin c.n) :
    ∃ q : Polynomial (ring c.U c.coefficientFunctions), q ≠ 0 ∧
      (∀ j, AnalyticOnNhd ℂ (representative c.U c.coefficientFunctions (q.coeff j)) c.U) ∧
      (¬ EqOn (representative c.U c.coefficientFunctions q.leadingCoeff) 0 c.U) ∧
      ∀ z : c.U, ∀ v, (∀ j, evaluate v (c.coefficients j z) = 0) →
        q.eval₂ (evaluation c.U c.coefficientFunctions z) (v i) = 0 := by
  obtain ⟨q, hq, ha, hl, he⟩ := analytic_coordinate_eliminant c.coefficientFunctions
    c.openU hconn hne c.coefficientFunctions_analytic c.ringIdeal
    (fun z => by rw [c.map_ringIdeal]; exact c.zeroLocus_finite z.property (hf z)) i
  refine ⟨q, hq, ha, hl, fun z v hv => he z v ?_⟩
  rw [c.map_ringIdeal]
  exact (c.mem_zeroLocus z v).mpr hv

#print axioms entry
#print axioms Presentation.coefficientFunctions_analytic
#print axioms Presentation.map_ringEquation
#print axioms Presentation.map_ringIdeal
#print axioms Presentation.zeroLocus_finite
#print axioms Presentation.coordinate_eliminant

end FinitenessAllLevelPolynomialPresentation
