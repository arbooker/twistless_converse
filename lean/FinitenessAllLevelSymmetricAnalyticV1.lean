module

public import FinitenessAllLevelFiniteSheetsV1
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Analysis.Analytic.Polynomial

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelPolynomialPresentation

open Complex Set Filter Polynomial
open scoped Topology

/-- Finite products of polynomial families with analytic coefficients
again have analytic coefficients. No topology on the full polynomial ring
is imposed. -/
theorem analytic_product_coeff {κ : Type*} (s : Finset κ) (P : κ → ℂ → Polynomial ℂ)
    {w : ℂ} (hP : ∀ i ∈ s, ∀ n, AnalyticAt ℂ (fun z => (P i z).coeff n) w) (n : ℕ) :
    AnalyticAt ℂ (fun z => (∏ i ∈ s, P i z).coeff n) w := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty => simpa only [Finset.prod_empty] using (analyticAt_const (v := (1 : Polynomial ℂ).coeff n))
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi, Polynomial.coeff_mul]
    apply Finset.analyticAt_fun_sum
    intro j _
    exact (hP i (Finset.mem_insert_self _ _) j.1).mul
      (ih (fun k hk => hP k (Finset.mem_insert_of_mem hk)) j.2)

/-- The elementary symmetric coefficients of finitely many holomorphic
functions are holomorphic, expressed as coefficients of their monic root
polynomial. -/
theorem analytic_root_product_coeff {κ : Type*} [Fintype κ] (b : κ → ℂ → ℂ)
    {w : ℂ} (hb : ∀ i, AnalyticAt ℂ (b i) w) (n : ℕ) :
    AnalyticAt ℂ (fun z => (∏ i, (Polynomial.X - Polynomial.C (b i z))).coeff n) w := by
  apply analytic_product_coeff
  intro i _ k
  simp only [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
  split_ifs <;> fun_prop

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The monic polynomial recording all observable values on an actual
finite fiber, with repetition when different points have the same value. -/
def fiberPolynomial (R : ℂ → X → Prop) (b : X → ℂ) (z : ℂ) : Polynomial ℂ :=
  ∏ᶠ x : {x | R z x}, (Polynomial.X - Polynomial.C (b x.val))

/-- Every coefficient of the actual fiber polynomial is holomorphic at a
regular value. Properness makes the locally enumerated root list exhaustive. -/
theorem fiberPolynomial_analytic_coeff (R : ℂ → X → Prop)
    (hp : IsProperMap (fun t : {t : ℂ × X | R t.1 t.2} => t.val.1))
    (b : X →L[ℂ] ℂ) (w : ℂ) (hf : {x | R w x}.Finite)
    (hg : ∀ x, R w x → AmbientGraphAt R w x) (n : ℕ) :
    AnalyticAt ℂ (fun z => (fiberPolynomial R b z).coeff n) w := by
  classical
  let := hf.fintype
  obtain ⟨F, _, ha, he⟩ := finite_sheets R hp w hf hg
  have han := analytic_root_product_coeff (fun x z => b (F x z))
    (fun x => (b.analyticAt (F x w)).comp (ha x)) n
  apply han.congr
  filter_upwards [he] with z hz
  let f : {x | R w x} → {x | R z x} := fun x => ⟨F x z, hz.1 x⟩
  have hi : Function.Injective f := fun x y h => hz.2.1 (congrArg Subtype.val h)
  have hs : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := hz.2.2 y.val y.property
    exact ⟨x, Subtype.ext hx⟩
  have heq := finprod_comp_equiv (Equiv.ofBijective f ⟨hi, hs⟩)
    (f := fun y : {x | R z x} => Polynomial.X - Polynomial.C (b y.val))
  have hpz : (∏ x : {x | R w x}, (Polynomial.X - Polynomial.C (b (F x z)))) =
      fiberPolynomial R b z := by
    change (∏ᶠ x : {x | R w x}, (Polynomial.X - Polynomial.C (b (F x z)))) =
      fiberPolynomial R b z at heq
    rw [finprod_eq_prod_of_fintype] at heq
    exact heq
  exact congrArg (fun p : Polynomial ℂ => p.coeff n) hpz

omit [NormedAddCommGroup X] [NormedSpace ℂ X] in
/-- Each actual observable value is a root, including at exceptional
parameters. This statement alone does not assert coefficient continuity
at the exceptional values. -/
theorem fiberPolynomial_eval_zero (R : ℂ → X → Prop) (b : X → ℂ)
    (z : ℂ) (hf : {x | R z x}.Finite) {x : X} (hx : R z x) :
    (fiberPolynomial R b z).eval (b x) = 0 := by
  classical
  let := hf.fintype
  simp only [fiberPolynomial, finprod_eq_prod_of_fintype, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact Finset.prod_eq_zero (Finset.mem_univ (⟨x, hx⟩ : {x | R z x})) (sub_self (b x))

#print axioms analytic_product_coeff
#print axioms analytic_root_product_coeff
#print axioms fiberPolynomial_analytic_coeff
#print axioms fiberPolynomial_eval_zero

end FinitenessAllLevelPolynomialPresentation
