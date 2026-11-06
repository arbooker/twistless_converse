module

public import FinitenessAllLevelSystemCertificateV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelPolynomialPresentation

open Complex Set Filter FinitenessAllLevelCoefficientRing FinitenessAllLevelQuadraticCoordinates
  FinitenessAllLevelFiniteFiberAlgebra FinitenessAllLevelAnalyticSubstitution
open scoped Topology

variable {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [Finite ι] {R : ℂ → X → Prop}

/-- Outside a fixed analytic exceptional set, EVERY actual solution point
lies on a unique holomorphic graph of actual solutions. There is no longer
an isolated-point alternative at these parameters. -/
theorem Presentation.BranchCertificate.local_graph (c : Presentation ι R)
    (D : c.BranchCertificate) (w : c.U)
    (hw : evaluation c.U c.coefficientFunctions w D.exceptional ≠ 0)
    (v : Fin c.n → ℂ) (hv : ∀ j, evaluate v (c.coefficients j w) = 0) :
    ∃ B : ℂ → (Fin c.n → ℂ), B w = v ∧ AnalyticAt ℂ B w ∧
      AnalyticAt ℂ (fun z => c.lift z (B z)) w ∧
      (∀ᶠ z in 𝓝 w.val, R z (c.lift z (B z))) ∧
      ∀ᶠ t in 𝓝 (w.val, v),
        (t.1 ∈ c.U ∧ ∀ j, evaluate t.2 (c.coefficients j t.1) = 0) ↔ t.2 = B t.1 := by
  obtain ⟨B, hBw, hB, hrect, hunique⟩ := rectangular_branch c.coefficientFunctions
    c.coefficientFunctions_analytic D.q w v (D.separable w hw) (D.contain w v hv)
  have hU : ∀ᶠ z in 𝓝 w.val, z ∈ c.U := c.openU.mem_nhds w.property
  have hfull : ∀ᶠ z in 𝓝 w.val, ∀ j, evaluate (B z) (c.coefficients j z) = 0 := by
    apply Filter.eventually_all.mpr
    intro j
    apply residual_stays_zero c.coefficientFunctions c.coefficientFunctions_analytic
      (D.s j) (D.multiplicity j) w (fun z => evaluate (B z) (c.coefficients j z))
      (c.graph_equation_analytic w.property hB j).continuousAt
      (by rw [hBw]; exact hv j) (D.residual_nonzero w hw j)
    filter_upwards [hU, hrect] with z hz he
    have heval (i : Fin c.n) :
        (D.q i).eval₂ (evaluation c.U c.coefficientFunctions ⟨z, hz⟩) (B z i) = 0 := by
      rw [← polynomialEquation_eq]
      exact he i
    have hid := eval_residual_certificate (evaluation c.U c.coefficientFunctions ⟨z, hz⟩)
      D.q (c.ringEquation j) (D.multiplicity j) (D.s j) (D.residual_identity j) (B z) heval
    rw [c.map_ringEquation, aeval_polynomial] at hid
    rw [polynomialEquation_eq (z := ⟨z, hz⟩)]
    exact hid
  refine ⟨B, hBw, hB, ?_, ?_, ?_⟩
  · exact (joint_analytic c.analytic_lift (w.val, B w)
      ⟨w.property, mem_univ _⟩).comp (f := fun z : ℂ => (z, B z)) (analyticAt_id.prod hB)
  · filter_upwards [hU, hfull] with z hz he
    exact (c.exact_locus z hz _).mpr ⟨B z, he, rfl⟩
  · have hfst : Tendsto (fun t : ℂ × (Fin c.n → ℂ) => t.1)
        (𝓝 (w.val, v)) (𝓝 w.val) := continuous_fst.continuousAt.tendsto
    filter_upwards [hunique, hfst.eventually hfull, hfst.eventually hU] with t ht he hu
    constructor
    · intro hzero
      apply ht.mp
      intro i
      rw [polynomialEquation_eq (z := ⟨t.1, hu⟩)]
      exact D.contain ⟨t.1, hu⟩ t.2 hzero.2 i
    · intro hb
      exact ⟨hu, hb ▸ he⟩

#print axioms Presentation.BranchCertificate.local_graph

end FinitenessAllLevelPolynomialPresentation
