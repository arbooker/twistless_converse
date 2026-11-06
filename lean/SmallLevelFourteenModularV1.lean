module

public import SmallLevelFourteenGeneratorsV1
public import SmallLevelModularCriterionV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace SmallLevelOriginal

open Matrix SmallLevelGenerators
open scoped MatrixGroups ModularForm

theorem gamma_zero_fourteen (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 14 (2*m) f)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 14) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] γ=fourierFunction (2*m) f := by
  let K := slashStabilizer ((2*m:ℕ):ℤ) (fourierFunction (2*m) f)
  have hK (i : Fin 7) : SmallLevelFourteen.generator i∈K := by
    fin_cases i
    · exact SmallLevelFourteen.original_kernel m hf 0
    · exact SmallLevelFourteen.original_kernel m hf 1
    · exact SmallLevelFourteen.original_kernel m hf 2
    · exact SmallLevelFourteen.original_kernel m hf 3
    · exact SmallLevelFourteen.original_kernel m hf 4
    · exact SmallLevelFourteen.original_kernel m hf 5
    · exact SmallLevelFourteen.original_A m hm hf
  change γ∈K
  exact SmallLevelFourteen.gamma0_mem K hK
    (SmallLevelThirtySix.slash_neg_one_even _ m) γ hγ

/-- Original level-fourteen Euler solutions are genuine modular forms for
every positive even weight, including holomorphy at all cusps. -/
theorem level_fourteen {k : ℕ} (hk : 0<k) (heven : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 14 k f) : IsModular 14 k f := by
  obtain ⟨m,hm⟩ := heven
  have hkm : k=2*m := by omega
  rw [hkm] at hf ⊢
  exact modular_of_transformations (by decide) hf (gamma_zero_fourteen m (by omega) hf)

#print axioms gamma_zero_fourteen
#print axioms level_fourteen

end SmallLevelOriginal
