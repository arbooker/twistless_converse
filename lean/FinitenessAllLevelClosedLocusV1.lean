module

public import FinitenessAllLevelHomeomorphicChartV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace FinitenessAllLevelConstraintLocus

open Complex Set Filter FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelGlobalHeight FinitenessAllLevelCertificatePencil
  FinitenessAllLevelCompactFredholm FinitenessAllLevelFredholmReduction
  QuantitativeArithmeticRetainedCertificate
open scoped Topology

/-- Exact finite charts make each constrained pencil locus closed in the
ambient Banach coordinate space. This holds without a bound on the eigenvalue. -/
theorem constrained_locus_isClosed {N Q p : ℕ} {hQ : 0 < Q}
    (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a b : ℝ} (hb : 0 < b) (hba : b < a) (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (m : ℕ) :
    IsClosed {t : ℂ × space (radius a) |
      pencil hN A hb hba χ m t.1 t.2 = t.2 ∧ Constraints A P a χ m t.1 t.2} := by
  apply IsSeqClosed.isClosed
  intro seq t hseq ht
  obtain ⟨D, hD, hC, V, s, hV, hw, hJ, hM, _, hs, hred⟩ :=
    exact_local_chart hN hp A P hb hba hae χ m t.1
  let J := fun z => lift D (defect (pencil hN A hb hba χ m z))
  let M := fun z => matrix D (defect (pencil hN A hb hba χ m z))
  let C := coordinate D
  have hz : Tendsto (fun n => (seq n).1) atTop (𝓝 t.1) := continuous_fst.continuousAt.tendsto.comp ht
  have hx : Tendsto (fun n => (seq n).2) atTop (𝓝 t.2) := continuous_snd.continuousAt.tendsto.comp ht
  have hc : Tendsto (fun n => C (seq n).2) atTop (𝓝 (C t.2)) := C.continuous.continuousAt.tendsto.comp hx
  have hVn : ∀ᶠ n in atTop, (seq n).1 ∈ V := hz.eventually (hV.mem_nhds hw)
  have he : ∀ᶠ n in atTop,
      (seq n).2 = J (seq n).1 (C (seq n).2) ∧
      M (seq n).1 (C (seq n).2) = 0 ∧
      ∀ e ∈ s, scalar A P a χ m e ((seq n).1, J (seq n).1 (C (seq n).2)) = 0 := by
    filter_upwards [hVn] with n hn
    obtain ⟨v, hmv, hv, hev⟩ := (hred (seq n).1 hn (seq n).2).mp (hseq n)
    have hcv : C (seq n).2 = v := by rw [hv]; exact coordinate_lift D _ v
    exact ⟨by rw [hcv]; exact hv, by rw [hcv]; exact hmv, by rw [hcv]; exact hev⟩
  have hjt : Tendsto (fun n => J (seq n).1 (C (seq n).2)) atTop
      (𝓝 (J t.1 (C t.2))) :=
    ((isBoundedBilinearMap_apply (𝕜 := ℂ) (E := D.decDom.X₀)
      (F := space (radius a))).continuous.continuousAt.tendsto).comp
      (((hJ t.1 hw).continuousAt.tendsto.comp hz).prodMk_nhds hc)
  have htJ : t.2 = J t.1 (C t.2) :=
    tendsto_nhds_unique hx (hjt.congr' (he.mono (fun _ h => h.1.symm)))
  have hmt : Tendsto (fun n => M (seq n).1 (C (seq n).2)) atTop
      (𝓝 (M t.1 (C t.2))) :=
    ((isBoundedBilinearMap_apply (𝕜 := ℂ) (E := D.decDom.X₀)
      (F := D.decCodom.X₀)).continuous.continuousAt.tendsto).comp
      (((hM t.1 hw).continuousAt.tendsto.comp hz).prodMk_nhds hc)
  have htM : M t.1 (C t.2) = 0 := tendsto_nhds_unique hmt
    (tendsto_const_nhds.congr' (he.mono (fun _ h => h.2.1.symm)))
  apply (hred t.1 hw t.2).mpr
  refine ⟨C t.2, htM, htJ, ?_⟩
  intro e hes
  have hst := ((hs e hes (t.1, C t.2) ⟨hw, mem_univ _⟩).continuousAt.tendsto).comp
    (hz.prodMk_nhds hc)
  exact tendsto_nhds_unique hst
    (tendsto_const_nhds.congr' (he.mono (fun _ h => (h.2.2 e hes).symm)))

#print axioms constrained_locus_isClosed

end FinitenessAllLevelConstraintLocus
