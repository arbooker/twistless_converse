module

public import FinitenessAllLevelChartTopologyV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace FinitenessAllLevelConstraintLocus

open Complex Set FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelGlobalHeight FinitenessAllLevelCertificatePencil
  FinitenessAllLevelCompactFredholm FinitenessAllLevelFredholmReduction
  FinitenessAllLevelChartTopology QuantitativeArithmeticRetainedCertificate

/-- The finite holomorphic equations give an actual homeomorphism onto the
constrained pencil locus, preserving the eigenvalue coordinate exactly. The
finite-sector identification with original solutions is finite_locus_iff_original. -/
theorem homeomorphic_local_chart {N Q p : ℕ} {hQ : 0 < Q}
    (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a b : ℝ} (hb : 0 < b) (hba : b < a) (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (m : ℕ) (w : ℂ) :
    ∃ D : (defect (pencil hN A hb hba χ m w)).FredholmPackage,
      FiniteDimensional ℂ D.decDom.X₀ ∧ FiniteDimensional ℂ D.decCodom.X₀ ∧
      ∃ V : Set ℂ, ∃ s : Finset (Index N Q), IsOpen V ∧ w ∈ V ∧
        AnalyticOnNhd ℂ (fun z => lift D (defect (pencil hN A hb hba χ m z))) V ∧
        AnalyticOnNhd ℂ (fun z => matrix D (defect (pencil hN A hb hba χ m z))) V ∧
        (∀ e ∈ s, AnalyticOnNhd ℂ (fun t : ℂ × D.decDom.X₀ =>
          scalar A P a χ m e (t.1, lift D (defect (pencil hN A hb hba χ m t.1)) t.2))
            (V ×ˢ univ)) ∧
        ∃ H : locus V (fun z (v : D.decDom.X₀) =>
            matrix D (defect (pencil hN A hb hba χ m z)) v = 0 ∧
            ∀ e ∈ s, scalar A P a χ m e (z, lift D (defect (pencil hN A hb hba χ m z)) v) = 0) ≃ₜ
          locus V (fun z (F : space (radius a)) =>
            pencil hN A hb hba χ m z F = F ∧ Constraints A P a χ m z F),
          ∀ t, (H t).val = (t.val.1, lift D (defect (pencil hN A hb hba χ m t.val.1)) t.val.2) := by
  obtain ⟨D, hD, hC, V, s, hV, hw, hJ, hM, _, hs, hred⟩ :=
    exact_local_chart hN hp A P hb hba hae χ m w
  refine ⟨D, hD, hC, V, s, hV, hw, hJ, hM, hs, ?_⟩
  have he (z : ℂ) (hz : z ∈ V) (F : space (radius a)) :
      (pencil hN A hb hba χ m z F = F ∧ Constraints A P a χ m z F) ↔
        ∃ v : D.decDom.X₀,
          (matrix D (defect (pencil hN A hb hba χ m z)) v = 0 ∧
            ∀ e ∈ s, scalar A P a χ m e (z, lift D (defect (pencil hN A hb hba χ m z)) v) = 0) ∧
          F = lift D (defect (pencil hN A hb hba χ m z)) v := by
    rw [hred z hz F]
    constructor
    · rintro ⟨v, hm, hf, he⟩
      exact ⟨v, ⟨hm, he⟩, hf⟩
    · rintro ⟨v, ⟨hm, he⟩, hf⟩
      exact ⟨v, hm, hf, he⟩
  exact ⟨reconstructionHomeomorph V _ _ (coordinate D)
    (fun z => lift D (defect (pencil hN A hb hba χ m z))) hJ.continuousOn
    (fun z v => coordinate_lift D _ v) he, fun _ => rfl⟩

#print axioms homeomorphic_local_chart

end FinitenessAllLevelConstraintLocus
