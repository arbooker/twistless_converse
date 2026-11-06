module

public import FinitenessAllLevelPolynomialPresentationV1
public import FinitenessAllLevelSectorAtlasV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace FinitenessAllLevelConstraintLocus

open Complex Set Module FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelGlobalHeight FinitenessAllLevelCertificatePencil
  FinitenessAllLevelCompactFredholm FinitenessAllLevelFredholmReduction
  FinitenessAllLevelFormalContinuation FinitenessAllLevelAnalyticSubstitution
  FinitenessAllLevelQuadraticCoordinates FinitenessAllLevelPolynomialPresentation
  QuantitativeArithmeticRetainedCertificate

/-- Every eigenvalue has an exact polynomial presentation of the original
sector, with holomorphic coefficients and injective reconstruction. -/
theorem sector_polynomial_presentation {N Q p : ℕ} {hQ : 0 < Q}
    (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a b : ℝ} (hb : 0 < b) (hba : b < a) (hae : a ≤ P.ε)
    (m : ℕ) (s : Fin (Q + 1) → Bool) (w : ℂ) :
    ∃ (d : ℕ) (es : Finset (Index N Q)),
      ∃ c : Presentation (Fin d ⊕ es)
        (fun z F => (z, F) ∈ sectorLocus hN A P hb hba m s), w ∈ c.U := by
  classical
  let χ := sector Q m s
  obtain ⟨D, hD, hC, V, es, hV, hw, hJ, hM, hJi, _, hred⟩ :=
    exact_local_chart hN hp A P hb hba hae χ m w
  let := hD
  let := hC
  let n := finrank ℂ D.decDom.X₀
  let d := finrank ℂ D.decCodom.X₀
  let bx : Basis (Fin n) ℂ D.decDom.X₀ := Module.finBasis ℂ D.decDom.X₀
  let by' : Basis (Fin d) ℂ D.decCodom.X₀ := Module.finBasis ℂ D.decCodom.X₀
  let J := fun z => lift D (defect (pencil hN A hb hba χ m z))
  let M := fun z => matrix D (defect (pencil hN A hb hba χ m z))
  let H : (Fin d ⊕ es) → ℂ × D.decDom.X₀ → ℂ := fun i t =>
    match i with
    | .inl j => by'.coord j (M t.1 t.2)
    | .inr e => scalar A P a χ m e.val (t.1, J t.1 t.2)
  have hH (i : Fin d ⊕ es) : Representable bx (U := V) (H i) := by
    cases i with
    | inl j =>
      apply represent_linear bx (fun z => (by'.coord j).comp (M z).toLinearMap)
      intro v z hz
      exact ((by'.coord j).toContinuousLinearMap.analyticAt _).comp
        ((joint_analytic hM (z, v) ⟨hz, mem_univ _⟩).comp
          (f := fun z : ℂ => (z, v)) (analyticAt_id.prod analyticAt_const))
    | inr e =>
      exact scalar_representable hN hp A P (hb.trans hba) hae χ m e.val bx hV hJ
  choose c hc he using hH
  have hzero (z : ℂ) (v : D.decDom.X₀) :
      (∀ i, evaluate (bx.repr v) (c i z) = 0) ↔
        M z v = 0 ∧ ∀ e ∈ es, scalar A P a χ m e (z, J z v) = 0 := by
    simp only [he]
    constructor
    · intro h
      refine ⟨?_, fun e he' => h (.inr ⟨e, he'⟩)⟩
      apply by'.repr.injective
      ext j
      simpa only [H, Basis.coord_apply, map_zero, Finsupp.zero_apply] using h (.inl j)
    · rintro ⟨hm, hs⟩ i
      cases i with
      | inl j => change by'.coord j (M z v) = 0; rw [hm, map_zero]
      | inr e => exact hs e.val e.property
  let e := bx.equivFun.symm.toContinuousLinearEquiv
  let J' : ℂ → (Fin n → ℂ) →L[ℂ] space (radius a) :=
    fun z => (J z).comp e.toContinuousLinearMap
  have hJ' : AnalyticOnNhd ℂ J' V := by
    intro z hz
    let C : (D.decDom.X₀ →L[ℂ] space (radius a)) →L[ℂ]
        ((Fin n → ℂ) →L[ℂ] space (radius a)) :=
      (ContinuousLinearMap.compL ℂ (Fin n → ℂ) D.decDom.X₀ (space (radius a))).flip
        e.toContinuousLinearMap
    exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ)
      (E := D.decDom.X₀ →L[ℂ] space (radius a))
      (F := (Fin n → ℂ) →L[ℂ] space (radius a)) C (J z)).comp (hJ z hz)
  let pr : Presentation (Fin d ⊕ es)
      (fun z F => (z, F) ∈ sectorLocus hN A P hb hba m s) := {
    n := n
    U := V
    openU := hV
    lift := J'
    analytic_lift := hJ'
    injective_lift := fun z => (hJi z).comp e.injective
    coefficients := c
    analytic_coefficients := hc
    exact_locus := by
      intro z hz F
      change (pencil hN A hb hba χ m z F = F ∧ Constraints A P a χ m z F) ↔ _
      rw [hred z hz F]
      constructor
      · rintro ⟨v, hm, hf, hs⟩
        refine ⟨bx.equivFun v, (hzero z v).mpr ⟨hm, hs⟩, ?_⟩
        change F = J z (bx.equivFun.symm (bx.equivFun v))
        simpa only [LinearEquiv.symm_apply_apply] using hf
      · rintro ⟨v, hv, hf⟩
        have hv' : ∀ i, evaluate (bx.repr (e v)) (c i z) = 0 := by
          change ∀ i, evaluate (bx.equivFun (bx.equivFun.symm v)) (c i z) = 0
          simpa only [LinearEquiv.apply_symm_apply] using hv
        obtain ⟨hm, hs⟩ := (hzero z (e v)).mp hv'
        exact ⟨e v, hm, hf, hs⟩ }
  exact ⟨d, es, pr, hw⟩

/-- The actual sector has locally finite-dimensional polynomial fiber
algebras, uniformly in the sense that one presentation works on a whole
open eigenvalue neighborhood. No eigenvalue bound is imposed. -/
theorem sector_finite_fiber_algebras {N Q p : ℕ} {hQ : 0 < Q}
    (hN : 0 < N) (hp : p.Prime) (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2)
    (hpQ : p ∣ Q) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a b : ℝ} (hb : 0 < b) (hba : b < a) (hae : a ≤ P.ε)
    {m : ℕ} (hm : 0 < m) (s : Fin (Q + 1) → Bool) (w : ℂ) :
    ∃ (d : ℕ) (es : Finset (Index N Q)),
      ∃ c : Presentation (Fin d ⊕ es)
        (fun z F => (z, F) ∈ sectorLocus hN A P hb hba m s),
        w ∈ c.U ∧ ∀ z ∈ c.U,
          FiniteDimensional ℂ (MvPolynomial (Fin c.n) ℂ ⧸ c.fiberIdeal z) := by
  obtain ⟨d, es, c, hw⟩ := sector_polynomial_presentation hN hp A P hb hba hae m s w
  exact ⟨d, es, c, hw, fun z hz => c.finiteDimensional_fiber hz
    (global_sector_fiber_finite hN hp hgood hlarge hpQ A P hb hba hae hm s z)⟩

#print axioms sector_polynomial_presentation
#print axioms sector_finite_fiber_algebras

end FinitenessAllLevelConstraintLocus
