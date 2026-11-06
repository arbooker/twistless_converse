module

public import FinitenessAllLevelPencilHeightsV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelOriginalPencil

open Complex Metric Set FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
  FinitenessAllLevelDiskAlgebra FinitenessAllLevelDiskSeries FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelBoundaryGeometry FinitenessAllLevelCertificateBoundary
  FinitenessAllLevelCertificatePencil FinitenessAllLevelPencilHeights
  FinitenessAllLevelReconstruction FinitenessAllLevelGlobalHeight FinitenessAllLevelGoodTrace
  FinitenessAllLevelCauchyTransform FinitenessAllLevelCauchyOperator
  QuantitativeArithmeticRetainedCertificate

variable {N Q p : ℕ} {hQ : 0 < Q}

/-- Every original solution is a fixed point of the actual compact pencil
in its derived root-number sector. All source evaluations are justified by
the strict upward-height estimate; none is an assumed extension of the disk input. -/
theorem original_fixedPoint (hN : 0 < N) (hp : p.Prime) (hgood : ¬ p ∣ N)
    (hpQ : p ∣ Q) (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    {a b : ℝ} (hb : 0 < b) (hab : b < a) (hbe : b ≤ P.ε) (hheight : a ≤ b / P.ρ)
    (m : ℕ) (f : S N (2 * m)) :
    ∃ χ : ℕ → ℂ, (∀ q, χ q = I ^ (2 * m) ∨ χ q = -I ^ (2 * m)) ∧
      (∀ q, ‖χ q‖ = 1) ∧
      FinitenessAllLevelCertificatePencil.pencil hN A hb hab χ m (f.val p)
        (representative N (2 * m) (radius_pos a) (radius_lt_one (hb.trans hab)) f) =
        representative N (2 * m) (radius_pos a) (radius_lt_one (hb.trans hab)) f := by
  obtain ⟨χ, hχ, hχnorm, hrec⟩ := original_reconstruction hN A
    (by intro q hq; simpa only [Finset.mem_singleton.mp hq] using hpQ)
    (by intro q hq; simpa only [Finset.mem_singleton.mp hq] using And.intro hp hgood) f.property
  refine ⟨χ, hχ, hχnorm, ?_⟩
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

/-- The initial and boundary heights are chosen before every weight and
original solution; only the root-number sector is selected afterwards. -/
theorem uniform_original_fixedPoints (hN : 0 < N) (hp : p.Prime) (hgood : ¬ p ∣ N)
    (hpQ : p ∣ Q) (A : Certificate N {p} Q hQ) :
    ∃ a b : ℝ, ∃ hb : 0 < b, ∃ hab : b < a, ∀ m : ℕ, ∀ f : S N (2 * m),
      ∃ χ : ℕ → ℂ, (∀ q, χ q = I ^ (2 * m) ∨ χ q = -I ^ (2 * m)) ∧
        (∀ q, ‖χ q‖ = 1) ∧
        FinitenessAllLevelCertificatePencil.pencil hN A hb hab χ m (f.val p)
          (representative N (2 * m) (radius_pos a) (radius_lt_one (hb.trans hab)) f) =
          representative N (2 * m) (radius_pos a) (radius_lt_one (hb.trans hab)) f := by
  obtain ⟨P⟩ := parameters_exist hN hQ A (by norm_num : (0 : ℝ) ≤ 0)
  obtain ⟨a, b, hb, hab, hbe, hheight⟩ := heights_exist A P
  exact ⟨a, b, hb, hab, fun m f => original_fixedPoint hN hp hgood hpQ A P hb hab hbe hheight m f⟩

#print axioms original_fixedPoint
#print axioms uniform_original_fixedPoints

end FinitenessAllLevelOriginalPencil
