module

public import QuantitativeMaassAdmissibleDivisorEigenV1
public import QuantitativeMaassCompletedHalfSignV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open AsymptoticClassicalPetersson AsymptoticSectorSigns QuantitativeNewGap QuantitativeNinaMaass
namespace QuantitativeMaass

/-- The original finite sign equations give unit eigenvalues for Fricke
and every canonical simple-prime normalizer on the actual quotient. -/
theorem countingSector_finite_unitEigen (N : ℕ) [NeZero N] (hN : 0<N)
    (e : Sector N) (x : AutomorphicSpace N) (hx : x∈completedCountingSectorSpace N hN e) :
    completedFrickeNormalizer N hN∈normalizerEigenStabilizer N x ∧
      ∀ p : SimplePrime N,completedLocalAtkinNormalizer N hN p∈normalizerEigenStabilizer N x := by
  have hs := (completedCountingSectorSpace_mem N hN e x).mp hx
  constructor
  · refine ⟨sign e.1,sign_norm e.1,?_⟩
    have he := hs.2 none
    change frickeIsometry N hN x=(signReal e.1:ℂ) • x at he
    rw [signReal_coe] at he
    exact he
  · intro p
    refine ⟨-delta e p.val,by rw [norm_neg,delta_norm],?_⟩
    have he := hs.2 (some p)
    change quotientNormalizerPullback N (completedLocalAtkinNormalizer N hN p) x=
      ((-signReal (e.2 p):ℝ):ℂ) • x at he
    simpa only [Complex.ofReal_neg,signReal_coe,delta,dite_eq_left p.property] using he

/-- Every elementary generator equation follows from the finite original
sign equations at an admissible level. Half translation uses actual newness. -/
theorem countingSector_generator_unitEigen (N : ℕ) [NeZero N]
    (hN : GridAdmissibleGap.Admissible N) (e : Sector N)
    (x : AutomorphicSpace N) (hx : x∈completedCountingSectorSpace N hN.1 e)
    (i : admissibleGeneratorIndex N hN.1) :
    admissibleGeneratorLift N hN.1 i∈normalizerEigenStabilizer N x := by
  obtain ⟨hW,hS⟩ := countingSector_finite_unitEigen N hN.1 e x hx
  have hnew := ((completedCountingSectorSpace_mem N hN.1 e x).mp hx).1.2
  obtain ⟨g,hg⟩ := i
  cases hg with
  | fricke => exact hW
  | half h4 =>
    refine ⟨-1,by norm_num,?_⟩
    change quotientNormalizerPullback N (completedHalfNormalizer N hN.1 h4) x=(-1:ℂ) • x
    exact (newSpace_half_completed N hN.1 h4 x hnew).trans (neg_one_smul ℂ x).symm
  | atkin D Q hQ A B hAB hQD =>
    have hcop : Nat.Coprime Q D := Nat.isCoprime_iff_coprime.mp ⟨A,B,by nlinarith [hAB]⟩
    exact admissible_divisorUnitEigen N hN x hW hS Q D hQD hcop
      ⟨exactAtkinLabel D Q hQ A B hAB,admissibleNormalizerGenerator.atkin D Q hQ A B hAB hQD⟩
      ⟨D,hQ,A,B,hAB,hQD,rfl⟩

/-- Existence of the full unit character is derived, not imposed as an
extra hypothesis on a finite physical sector. -/
theorem countingSector_character_extension (N : ℕ) [NeZero N]
    (hN : GridAdmissibleGap.Admissible N) (e : Sector N)
    (x : AutomorphicSpace N) (hx : x∈completedCountingSectorSpace N hN.1 e) :
    ∃ χ : admissibleGeneratorIndex N hN.1 → ℂ,(∀ i,‖χ i‖=1) ∧
      x∈completedNewSignSpace N hN.1 χ := by
  classical
  have hu (i : admissibleGeneratorIndex N hN.1) :
      ∃ c : ℂ,‖c‖=1 ∧ quotientNormalizerPullback N (admissibleGeneratorLift N hN.1 i) x=c • x :=
    countingSector_generator_unitEigen N hN e x hx i
  choose χ hχ he using hu
  have hs := (completedCountingSectorSpace_mem N hN.1 e x).mp hx
  exact ⟨χ,hχ,hs.1.1,hs.1.2,he⟩

#print axioms countingSector_finite_unitEigen
#print axioms countingSector_generator_unitEigen
#print axioms countingSector_character_extension
end QuantitativeMaass
