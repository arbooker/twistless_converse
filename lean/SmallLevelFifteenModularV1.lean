module

public import SmallLevelFifteenGeneratorsV1
public import SmallLevelModularCriterionV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace SmallLevelOriginal

open Matrix SmallLevelGenerators
open scoped MatrixGroups ModularForm

theorem gamma_zero_fifteen (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 15 (2*m) f)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 15) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] γ=fourierFunction (2*m) f := by
  let K := slashStabilizer ((2*m:ℕ):ℤ) (fourierFunction (2*m) f)
  have hK (i : Fin 7) : SmallLevelFifteen.generator i∈K := by
    fin_cases i
    · exact SmallLevelFifteen.original_kernel m hm hf 0
    · exact SmallLevelFifteen.original_kernel m hm hf 1
    · exact SmallLevelFifteen.original_kernel m hm hf 2
    · exact SmallLevelFifteen.original_kernel m hm hf 3
    · exact SmallLevelFifteen.original_kernel m hm hf 4
    · exact SmallLevelFifteen.original_kernel m hm hf 5
    · exact SmallLevelFifteen.original_kernel m hm hf 6
  change γ∈K
  exact SmallLevelFifteen.gamma0_mem K hK
    (SmallLevelThirtySix.slash_neg_one_even _ m) γ hγ

/-- Original level-fifteen Euler solutions are genuine modular forms for
every positive even weight, including holomorphy at all cusps. -/
theorem level_fifteen {k : ℕ} (hk : 0<k) (heven : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 15 k f) : IsModular 15 k f := by
  obtain ⟨m,hm⟩ := heven
  have hkm : k=2*m := by omega
  rw [hkm] at hf ⊢
  exact modular_of_transformations (by decide) hf (gamma_zero_fifteen m (by omega) hf)

#print axioms gamma_zero_fifteen
#print axioms level_fifteen

end SmallLevelOriginal
