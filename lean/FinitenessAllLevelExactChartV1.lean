module

public import FinitenessAllLevelLocalEquationsV1
public import FinitenessAllLevelPencilFredholmV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelConstraintLocus

open Complex Set FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelGlobalHeight FinitenessAllLevelCertificatePencil
  FinitenessAllLevelCompactFredholm FinitenessAllLevelFredholmReduction
  FinitenessAllLevelPencilFredholm QuantitativeArithmeticRetainedCertificate

/-- The actual compact pencil together with ALL original analytic and Euler
constraints has an exact local finite-dimensional description by finitely many
holomorphic equations. The reconstruction coordinate is injective. -/
theorem exact_local_chart {N Q p : ℕ} {hQ : 0 < Q}
    (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a b : ℝ} (hb : 0 < b) (hba : b < a) (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (m : ℕ) (w : ℂ) :
    ∃ D : (defect (pencil hN A hb hba χ m w)).FredholmPackage,
      FiniteDimensional ℂ D.decDom.X₀ ∧ FiniteDimensional ℂ D.decCodom.X₀ ∧
      ∃ V : Set ℂ, ∃ s : Finset (Index N Q), IsOpen V ∧ w ∈ V ∧
        AnalyticOnNhd ℂ (fun z => lift D (defect (pencil hN A hb hba χ m z))) V ∧
        AnalyticOnNhd ℂ (fun z => matrix D (defect (pencil hN A hb hba χ m z))) V ∧
        (∀ z, Function.Injective (lift D (defect (pencil hN A hb hba χ m z)))) ∧
        (∀ e ∈ s, AnalyticOnNhd ℂ (fun t : ℂ × D.decDom.X₀ =>
          scalar A P a χ m e (t.1, lift D (defect (pencil hN A hb hba χ m t.1)) t.2))
            (V ×ˢ univ)) ∧
        ∀ z ∈ V, ∀ F : space (radius a),
          (pencil hN A hb hba χ m z F = F ∧ Constraints A P a χ m z F) ↔
            ∃ v : D.decDom.X₀,
              matrix D (defect (pencil hN A hb hba χ m z)) v = 0 ∧
              F = lift D (defect (pencil hN A hb hba χ m z)) v ∧
              ∀ e ∈ s, scalar A P a χ m e
                (z, lift D (defect (pencil hN A hb hba χ m z)) v) = 0 := by
  obtain ⟨D, hD, hC, U, hU, hwU, hJ, hM, hred⟩ := pencil_local_reduction hN A hb hba χ m w
  let := hD
  let := hC
  obtain ⟨s, V, hV, hwV, hVU, hscalar, he⟩ :=
    finite_constraints_local hN hp A P (hb.trans hba) hae χ m hU hJ hwU
  refine ⟨D, hD, hC, V, s, hV, hwV, hJ.mono hVU, hM.mono hVU,
    fun z => lift_injective D _, hscalar, ?_⟩
  intro z hz F
  constructor
  · rintro ⟨hfix, hc⟩
    obtain ⟨v, hMv, hF⟩ := (hred z (hVU hz) F).mp hfix
    refine ⟨v, hMv, hF, (he z hz v).mp ?_⟩
    exact hF ▸ hc
  · rintro ⟨v, hMv, hF, hzero⟩
    refine ⟨(hred z (hVU hz) F).mpr ⟨v, hMv, hF⟩, ?_⟩
    rw [hF]
    exact (he z hz v).mpr hzero

#print axioms exact_local_chart

end FinitenessAllLevelConstraintLocus
