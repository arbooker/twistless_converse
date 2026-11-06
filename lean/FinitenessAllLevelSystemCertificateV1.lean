module

public import FinitenessAllLevelRectangularBranchesV1
public import FinitenessAllLevelRegularModelsV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelPolynomialPresentation

open Complex Set MvPolynomial FinitenessAllLevelCoefficientRing
  FinitenessAllLevelQuadraticCoordinates FinitenessAllLevelFiniteFiberAlgebra

variable {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {R : ℂ → X → Prop}

/-- Explicit polynomial certificates for continuation of the FULL equation
system. The residual identities prevent scalar branches from departing
from the original equations away from the exception function. -/
structure Presentation.BranchCertificate (c : Presentation ι R) where
  q : Fin c.n → Polynomial (ring c.U c.coefficientFunctions)
  s : ι → Polynomial (ring c.U c.coefficientFunctions)
  multiplicity : ι → ℕ
  exceptional : ring c.U c.coefficientFunctions
  exceptional_ne_zero : exceptional ≠ 0
  separable : ∀ w : c.U, evaluation c.U c.coefficientFunctions w exceptional ≠ 0 →
    ∀ i, ((q i).map (evaluation c.U c.coefficientFunctions w)).Separable
  residual_nonzero : ∀ w : c.U, evaluation c.U c.coefficientFunctions w exceptional ≠ 0 →
    ∀ j, evaluation c.U c.coefficientFunctions w ((s j).coeff 0) ≠ 0
  contain : ∀ z : c.U, ∀ v, (∀ j, evaluate v (c.coefficients j z) = 0) →
    ∀ i, (q i).eval₂ (evaluation c.U c.coefficientFunctions z) (v i) = 0
  residual_identity : ∀ j, Polynomial.aeval (c.ringEquation j)
    (Polynomial.X ^ multiplicity j * s j) ∈ rectangleIdeal q

/-- The branch certificates are constructed from actual finite fibers,
not assumed as an analytic continuation theorem. -/
theorem Presentation.exists_branchCertificate [Finite ι] (c : Presentation ι R)
    (hconn : IsPreconnected c.U) (hne : c.U.Nonempty)
    (hf : ∀ z : ℂ, {t : ℂ × X | R t.1 t.2 ∧ t.1 = z}.Finite) :
    Nonempty c.BranchCertificate := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨w, _, hw⟩ := exists_injective_evaluation c.U c.coefficientFunctions hconn
    c.coefficientFunctions_analytic c.openU (Subset.refl c.U) hne
  let := Function.Injective.isDomain (evaluation c.U c.coefficientFunctions w) hw
  obtain ⟨a, ha, he⟩ := exceptional_scalar c.coefficientFunctions c.openU hconn hne
    c.coefficientFunctions_analytic c.ringIdeal
    (fun z => by rw [c.map_ringIdeal]; exact c.zeroLocus_finite z.property (hf z))
  choose q hq hs hz using he
  have hres j := rectangular_residual_certificate
    (evaluation c.U c.coefficientFunctions w) hw q hq (c.ringEquation j)
  choose n s hsn hcert using hres
  have hgood (z : c.U)
      (h : evaluation c.U c.coefficientFunctions z (a * ∏ j, (s j).coeff 0) ≠ 0) :
      evaluation c.U c.coefficientFunctions z a ≠ 0 ∧
      ∀ j, evaluation c.U c.coefficientFunctions z ((s j).coeff 0) ≠ 0 := by
    rw [map_mul, map_prod, mul_ne_zero_iff] at h
    exact ⟨h.1, fun j => Finset.prod_ne_zero_iff.mp h.2 j (Finset.mem_univ j)⟩
  refine ⟨{
    q := q
    s := s
    multiplicity := n
    exceptional := a * ∏ j, (s j).coeff 0
    exceptional_ne_zero := mul_ne_zero ha (Finset.prod_ne_zero_iff.mpr (fun j _ => hsn j))
    separable := fun z h i => hs i z (hgood z h).1
    residual_nonzero := fun z h => (hgood z h).2
    contain := ?_
    residual_identity := hcert }⟩
  intro z v hv i
  apply hz i z v
  rw [c.map_ringIdeal]
  exact (c.mem_zeroLocus z v).mpr hv

#print axioms Presentation.exists_branchCertificate

end FinitenessAllLevelPolynomialPresentation
