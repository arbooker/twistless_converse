module

public import FinitenessAllLevelAnalyticAtlasV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace FinitenessAllLevelConstraintLocus

open Complex Set FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelGlobalHeight FinitenessAllLevelCertificatePencil
  FinitenessAllLevelCompactFredholm FinitenessAllLevelFredholmReduction
  FinitenessAllLevelFormalContinuation FinitenessAllLevelAnalyticAtlas
  FinitenessAllLevelAnalyticSubstitution QuantitativeArithmeticRetainedCertificate

/-- At every eigenvalue, a fixed exact sector has a finite-dimensional
holomorphic zero-set chart with actual reconstruction and coordinate maps.
The generic Chart theorems prove topology and holomorphic transition cocycles. -/
theorem sector_chart_exists {N Q p : ℕ} {hQ : 0 < Q}
    (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a b : ℝ} (hb : 0 < b) (hba : b < a) (hae : a ≤ P.ε)
    (m : ℕ) (s : Fin (Q + 1) → Bool) (w : ℂ) :
    ∃ c : Chart (Index N Q) (fun z F => (z, F) ∈ sectorLocus hN A P hb hba m s), w ∈ c.U := by
  let χ := sector Q m s
  obtain ⟨D, hD, hC, V, es, hV, hw, hJ, hM, _, hs, hred⟩ :=
    exact_local_chart hN hp A P hb hba hae χ m w
  let J := fun z => lift D (defect (pencil hN A hb hba χ m z))
  let M := fun z => matrix D (defect (pencil hN A hb hba χ m z))
  let H : ℂ × D.decDom.X₀ → D.decCodom.X₀ × (es → ℂ) :=
    fun t => (M t.1 t.2, fun e => scalar A P a χ m e.val (t.1, J t.1 t.2))
  have hH : AnalyticOnNhd ℂ H (V ×ˢ univ) := by
    intro t ht
    exact (joint_analytic hM t ht).prod
      (AnalyticAt.pi (fun e : es => hs e.val e.property t ht))
  have hzero (z : ℂ) (v : D.decDom.X₀) : H (z, v) = 0 ↔
      M z v = 0 ∧ ∀ e ∈ es, scalar A P a χ m e (z, J z v) = 0 := by
    constructor
    · intro he
      refine ⟨congrArg Prod.fst he, fun e he' => ?_⟩
      exact congrFun (congrArg Prod.snd he) ⟨e, he'⟩
    · rintro ⟨hm, he⟩
      exact Prod.ext hm (funext (fun e => he e.val e.property))
  let c : Chart (Index N Q) (fun z F => (z, F) ∈ sectorLocus hN A P hb hba m s) := {
    E := D.decDom.X₀
    Y := D.decCodom.X₀
    finiteE := hD
    finiteY := hC
    U := V
    openU := hV
    indices := es
    read := coordinate D
    lift := J
    equations := H
    analytic_lift := hJ
    analytic_equations := hH
    read_lift := fun z v => coordinate_lift D _ v
    exact_locus := by
      intro z hz F
      change (pencil hN A hb hba χ m z F = F ∧ Constraints A P a χ m z F) ↔ _
      rw [hred z hz F]
      constructor
      · rintro ⟨v, hm, hf, he⟩
        exact ⟨v, (hzero z v).mpr ⟨hm, he⟩, hf⟩
      · rintro ⟨v, hv, hf⟩
        obtain ⟨hm, he⟩ := (hzero z v).mp hv
        exact ⟨v, hm, hf, he⟩ }
  exact ⟨c, hw⟩

/-- A global covering family of compatible analytic zero-set charts. -/
def sectorAtlas {N Q p : ℕ} {hQ : 0 < Q}
    (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a b : ℝ} (hb : 0 < b) (hba : b < a) (hae : a ≤ P.ε)
    (m : ℕ) (s : Fin (Q + 1) → Bool) (w : ℂ) :
    Chart (Index N Q) (fun z F => (z, F) ∈ sectorLocus hN A P hb hba m s) :=
  (sector_chart_exists hN hp A P hb hba hae m s w).choose

theorem mem_sectorAtlas {N Q p : ℕ} {hQ : 0 < Q}
    (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a b : ℝ} (hb : 0 < b) (hba : b < a) (hae : a ≤ P.ε)
    (m : ℕ) (s : Fin (Q + 1) → Bool) (w : ℂ) :
    w ∈ (sectorAtlas hN hp A P hb hba hae m s w).U :=
  (sector_chart_exists hN hp A P hb hba hae m s w).choose_spec

#print axioms sector_chart_exists
#print axioms sectorAtlas
#print axioms mem_sectorAtlas

end FinitenessAllLevelConstraintLocus
