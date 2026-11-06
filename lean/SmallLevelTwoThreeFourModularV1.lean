module

public import SmallLevelTwoThreeFourGeneratorsV1
public import SmallLevelFrickeGeneratorsV1
public import SmallLevelModularCriterionV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace SmallLevelOriginal

open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups ModularForm

/-- All transformations at levels two, three and four follow from the
original untwisted functional equation and Fourier periodicity. -/
theorem gamma_zero_two_three_four {N : ℕ} (hN : N=2 ∨ N=3 ∨ N=4)
    (m : ℕ) {f : ℕ → ℂ} (hf : FinitenessOriginalInput.IsSolution N (2*m) f)
    (γ : SL(2,ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] γ=fourierFunction (2*m) f := by
  let K := slashStabilizer ((2*m:ℕ):ℤ) (fourierFunction (2*m) f)
  have ht : T ∈ K := original_T (2*m) f
  have hu : lower N ∈ K := original_lower (by omega) hf
  have hz : -1 ∈ K := SmallLevelThirtySix.slash_neg_one_even _ m
  change γ ∈ K
  rcases hN with rfl | rfl | rfl
  · exact gamma0_2_mem K ht hu hz γ hγ
  · exact gamma0_3_mem K ht hu hz γ hγ
  · exact gamma0_4_mem K ht hu hz γ hγ

/-- Genuine modular-form membership, including every cusp condition, for
the literal original solutions at levels 2, 3 and 4 and every even weight. -/
theorem levels_two_three_four {N k : ℕ} (hN : N=2 ∨ N=3 ∨ N=4)
    (heven : Even k) {f : ℕ → ℂ} (hf : FinitenessOriginalInput.IsSolution N k f) :
    IsModular N k f := by
  obtain ⟨m,hm⟩ := heven
  have hk : k=2*m := by omega
  rw [hk] at hf ⊢
  exact modular_of_transformations (by omega) hf (gamma_zero_two_three_four hN m hf)

theorem level_two {k : ℕ} (heven : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 2 k f) : IsModular 2 k f :=
  levels_two_three_four (Or.inl rfl) heven hf

theorem level_three {k : ℕ} (heven : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 3 k f) : IsModular 3 k f :=
  levels_two_three_four (Or.inr (Or.inl rfl)) heven hf

theorem level_four {k : ℕ} (heven : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 4 k f) : IsModular 4 k f :=
  levels_two_three_four (Or.inr (Or.inr rfl)) heven hf

#print axioms gamma_zero_two_three_four
#print axioms levels_two_three_four
#print axioms level_two
#print axioms level_three
#print axioms level_four

end SmallLevelOriginal
