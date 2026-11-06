module

public import FinitenessAllLevelFiniteSectorsV1
public import FinitenessAllLevelExactChartV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelOriginalPencil

open Complex Metric Set FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
  FinitenessAllLevelDiskAlgebra FinitenessAllLevelDiskSeries FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelBoundaryGeometry FinitenessAllLevelCertificateBoundary
  FinitenessAllLevelCertificatePencil FinitenessAllLevelPencilHeights
  FinitenessAllLevelReconstruction FinitenessAllLevelGlobalHeight FinitenessAllLevelGoodTrace
  FinitenessAllLevelCauchyTransform FinitenessAllLevelCauchyOperator
  FinitenessAllLevelFormalContinuation FinitenessAllLevelConstraintLocus
  FinitenessAllLevelCauchyConstraints
  QuantitativeArithmeticRetainedCertificate

variable {N Q p : ℕ} {hQ : 0 < Q}

/-- The compact pencil uses the same root sector as the displayed actual
functional equations. Sector choice is not repeated independently. -/
theorem fixedPoint_of_original_laws (hN : 0 < N) (hp : p.Prime) (hgood : ¬ p ∣ N)
    (hpQ : p ∣ Q) (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    {a b : ℝ} (hb : 0 < b) (hab : b < a) (hbe : b ≤ P.ε) (hheight : a ≤ b / P.ρ)
    (m : ℕ) (f : S N (2 * m)) (χ : ℕ → ℂ)
    (hFE : FinitenessHolomorphicSpace.Laws N Q χ m (fourier (fullCoefficients f.val (2 * m)))) :
    pencil hN A hb hab χ m (f.val p)
      (representative N (2 * m) (radius_pos a) (radius_lt_one (hb.trans hab)) f) =
      representative N (2 * m) (radius_pos a) (radius_lt_one (hb.trans hab)) f := by
  have hrec (j : Fin Q) (z : ℂ) (hz : 0 < z.im) :=
    reconstruct_FE_two_dilations A
      (by intro q hq; simpa only [Finset.mem_singleton.mp hq] using hpQ)
      (fourier (fullCoefficients f.val (2 * m))) (periodic _) (2 * m) χ
      (firstMultiplier f.val m) (fun q => (q : ℂ) ^ (2 * m)) hFE
      (by
        intro q hq w hw
        have heq : q = p := Finset.mem_singleton.mp hq
        subst q
        exact original_complete_even f.property.toEulerData hp hgood m hw) j z hz
  let F := representative N (2 * m) (radius_pos a) (radius_lt_one (hb.trans hab)) f
  let G := FinitenessPolynomialSeries.sum (fullCoefficients f.val (2 * m))
  have hpoly := FinitenessOriginalDiskIndependence.polynomial N (2 * m) f
  have he : EqOn ((boundary₀ hN A (radius a) hb χ m).data F +
      (f.val p) • (boundary₁ A (radius a) b m).data F) G (sphere (0 : ℂ) (radius b)) := by
    intro w hw
    change (boundary₀ hN A (radius a) hb χ m).data F w +
      f.val p * (boundary₁ A (radius a) b m).data F w = G w
    rw [boundary_formula]
    have hrow := hrec (selector Q hQ w) (line (coordinate w) b) (by simpa only [line_im] using hb)
    calc
      _ = ∑ i ∈ (A.coeff (selector Q hQ w)).support,
          (A.coeff (selector Q hQ w) i : ℂ) *
            twoDilationRow (fourier (fullCoefficients f.val (2 * m))) (2 * m) χ
              (firstMultiplier f.val m) (fun q => (q : ℂ) ^ (2 * m))
              (selector Q hQ w) (line (coordinate w) b) i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [rows_agree hN hp A P hb hbe hheight (lift F)
          (fourier (fullCoefficients f.val (2 * m)))
          (fun z hz => lift_representative f (hb.trans hab) hz) χ
          (firstMultiplier (fun _ => f.val p) m) (fun q => (q : ℂ) ^ (2 * m)) (2 * m) w i hi]
        congr 1
        cases i with
        | inl i => rfl
        | inr i =>
          have hpi : i.1.val = p := by simpa using i.1.property
          simp only [twoDilationRow, firstMultiplier, hpi]
      _ = fourier (fullCoefficients f.val (2 * m)) (line (coordinate w) b) := hrow.symm
      _ = G w := by
        unfold fourier
        rw [qParam_coordinate hw]
  have hG : DiffContOnCl ℂ G (ball 0 (radius b)) := by
    apply DifferentiableOn.diffContOnCl
    apply (FinitenessPolynomialSeries.holomorphic hpoly).mono
    exact closure_ball_subset_closedBall.trans (closedBall_subset_ball (radius_lt_one hb))
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  change (FinitenessAllLevelCertificatePencil.pencil hN A hb hab χ m (f.val p) F).val z = F.val z
  rw [pencil_apply, positive_congr (radius_pos b).le he,
    positive_eq (radius_pos b) hG (closedBall_subset_ball (radius_strictAnti hab) z.property)]
  have hG0 : G 0 = 0 := FinitenessPolynomialSeries.zero (fullCoefficients_zero f.property.zero _)
  rw [hG0, sub_zero]
  exact (FinitenessAllLevelTopology.polynomial_diskSeries_apply hpoly (radius_pos a).le
    (radius_lt_one (hb.trans hab)) z).symm

/-- A coherent given sector supplies all exact constraints. -/
theorem constraints_of_original_laws (hN : 0 < N) (hp : p.Prime) (hgood : ¬ p ∣ N)
    (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    {a : ℝ} (ha : 0 < a) (m : ℕ) (f : S N (2 * m)) (χ : ℕ → ℂ)
    (hFE : FinitenessHolomorphicSpace.Laws N Q χ m (fourier (fullCoefficients f.val (2 * m))))
    (he : ∀ z : ℂ, 0 < z.im → formal A P a χ m (f.val p)
      (representative N (2 * m) (radius_pos a) (radius_lt_one ha) f) z =
        fourier (fullCoefficients f.val (2 * m)) z) :
    Constraints A P a χ m (f.val p)
      (representative N (2 * m) (radius_pos a) (radius_lt_one ha) f) := by
  constructor
  · apply identities_of_differentiableOn
    apply (show DifferentiableOn ℂ (fourier (fullCoefficients f.val (2 * m)))
        {z : ℂ | 0 < z.im} from fun z hz =>
      (holomorphic (FinitenessOriginalDiskIndependence.polynomial N (2 * m) f) hz).differentiableWithinAt).congr
    exact he
  · intro q hq z hz
    have hL : 0 < Nat.lcm N (q ^ 2) := Nat.lcm_pos hN (pow_pos (Nat.pos_of_dvd_of_pos hq hQ) _)
    have hr : 0 < (-1 / ((Nat.lcm N (q ^ 2) : ℕ) * z)).im := by
      simpa only [ofReal_natCast] using FinitenessComplexGeometry.reflected_im_pos
        (L := (Nat.lcm N (q ^ 2) : ℝ)) (by exact_mod_cast hL) hz
    rw [twist_congr_upper he q hz, twist_congr_upper he q hr]
    exact hFE q hq z hz
  · intro z hz
    have hz1 : 0 < ((p : ℂ) * z).im := by
      simpa using mul_pos (Nat.cast_pos.mpr hp.pos : (0 : ℝ) < p) hz
    have hz2 : 0 < ((p : ℂ) ^ 2 * z).im := by
      simpa only [← ofReal_natCast, ← ofReal_pow, mul_im, ofReal_re, ofReal_im,
        zero_mul, add_zero] using mul_pos (pow_pos (Nat.cast_pos.mpr hp.pos : (0 : ℝ) < p) 2) hz
    rw [complete_congr_upper he p hz, he _ hz1, he _ hz2]
    exact original_complete_even f.property.toEulerData hp hgood m hz
  · exact FinitenessAllLevelEulerEquations.original_equations p (radius_pos a) (radius_lt_one ha) f

/-- Every original solution belongs to the constrained compact pencil in
one of a fixed finite set of root sectors, with a single coherent choice. -/
theorem original_finite_constrained_pencil
    (hN : 0 < N) (hp : p.Prime) (hgood : ¬ p ∣ N) (hpQ : p ∣ Q)
    (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    {a b : ℝ} (hb : 0 < b) (hab : b < a) (hae : a ≤ P.ε) (hheight : a ≤ b / P.ρ)
    (m : ℕ) (f : S N (2 * m)) :
    ∃ s : Fin (Q + 1) → Bool,
      let F := representative N (2 * m) (radius_pos a) (radius_lt_one (hb.trans hab)) f
      pencil hN A hb hab (sector Q m s) m (f.val p) F = F ∧
      Constraints A P a (sector Q m s) m (f.val p) F := by
  obtain ⟨χ, hs, _, hFE, he⟩ :=
    original_formal_with_laws hN hp hgood hpQ A P (hb.trans hab) hae m f
  obtain ⟨s, hsec⟩ := exists_sector hQ m χ hs
  have hFE' : FinitenessHolomorphicSpace.Laws N Q (sector Q m s) m
      (fourier (fullCoefficients f.val (2 * m))) := by
    intro q hq z hz
    rw [hsec q hq]
    exact hFE q hq z hz
  refine ⟨s, fixedPoint_of_original_laws hN hp hgood hpQ A P hb hab
    (hab.le.trans hae) hheight m f _ hFE', ?_⟩
  apply constraints_of_original_laws hN hp hgood A P (hb.trans hab) m f _ hFE'
  intro z hz
  exact (formal_sector_congr A P hsec a m (f.val p) _ z).trans (he z hz)

#print axioms fixedPoint_of_original_laws
#print axioms constraints_of_original_laws
#print axioms original_finite_constrained_pencil

end FinitenessAllLevelOriginalPencil
