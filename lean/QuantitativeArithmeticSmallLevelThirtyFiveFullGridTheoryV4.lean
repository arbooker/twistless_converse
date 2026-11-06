module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Tactic
public import QuantitativeArithmeticFiniteAnalyticWitnessV1
public import QuantitativeArithmeticSmallLevelThirtyFiveFullGridCaseIndexDataSeriesV4
public import QuantitativeArithmeticSmallLevelThirtyFiveFullGridCaseIndexKernelSeriesV4

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelThirtyFiveFullGrid. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveFullGridCaseIndexLinearPartsBundleSeriesV4 -/
section
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 4000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyFiveFullGrid

def selectedPartLinear0_0 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart0_0 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart0_0]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart0_0]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1
def selectedPartLinear0_1 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart0_1 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart0_1]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart0_1]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1
def selectedPartLinear0_2 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart0_2 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart0_2]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart0_2]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1

def selectedPartLinear0_3 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart0_3 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart0_3]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart0_3]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1
def selectedPartLinear0_4 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart0_4 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart0_4]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart0_4]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1
def selectedPartLinear0_5 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart0_5 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart0_5]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart0_5]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1

def selectedPartLinear0_6 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart0_6 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart0_6]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart0_6]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1
def selectedPartLinear0_7 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart0_7 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart0_7]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart0_7]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1
def selectedPartLinear0_8 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart0_8 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart0_8]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart0_8]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1

def selectedPartLinear0_9 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart0_9 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart0_9]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart0_9]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1
def selectedPartLinear0_10 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart0_10 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart0_10]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart0_10]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1
def selectedPartLinear0_11 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart0_11 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart0_11]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart0_11]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1

def selectedPartLinear0_12 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart0_12 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart0_12]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart0_12]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1
def selectedPartLinear0_13 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart0_13 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart0_13]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart0_13]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1
def selectedPartLinear0_14 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart0_14 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart0_14]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart0_14]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1

def selectedPartLinear0_15 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart0_15 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart0_15]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart0_15]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1
def selectedPartLinear0_16 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart0_16 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart0_16]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart0_16]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1
def selectedPartLinear0_17 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart0_17 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart0_17]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart0_17]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1

def selectedPartLinear0_18 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart0_18 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart0_18]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart0_18]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1
def selectedPartLinear0_19 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart0_19 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart0_19]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart0_19]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1
def selectedPartLinear0_20 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart0_20 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart0_20]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart0_20]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1

end QuantitativeArithmeticSmallLevelThirtyFiveFullGrid
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 4000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyFiveFullGrid

def selectedPartLinear1_0 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart1_0 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart1_0]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart1_0]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1
def selectedPartLinear1_1 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart1_1 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart1_1]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart1_1]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1
def selectedPartLinear1_2 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart1_2 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart1_2]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart1_2]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1

def selectedPartLinear1_3 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart1_3 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart1_3]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart1_3]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1
def selectedPartLinear1_4 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart1_4 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart1_4]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart1_4]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1
def selectedPartLinear1_5 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart1_5 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart1_5]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart1_5]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1

def selectedPartLinear1_6 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart1_6 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart1_6]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart1_6]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1
def selectedPartLinear1_7 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart1_7 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart1_7]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart1_7]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1
def selectedPartLinear1_8 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart1_8 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart1_8]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart1_8]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1

def selectedPartLinear1_9 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart1_9 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart1_9]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart1_9]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1
def selectedPartLinear1_10 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart1_10 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart1_10]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart1_10]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1
def selectedPartLinear1_11 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart1_11 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart1_11]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart1_11]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1

def selectedPartLinear1_12 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart1_12 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart1_12]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart1_12]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1
def selectedPartLinear1_13 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart1_13 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart1_13]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart1_13]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1
def selectedPartLinear1_14 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart1_14 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart1_14]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart1_14]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1

def selectedPartLinear1_15 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart1_15 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart1_15]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart1_15]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1
def selectedPartLinear1_16 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart1_16 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart1_16]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart1_16]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1
def selectedPartLinear1_17 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart1_17 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart1_17]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart1_17]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1

def selectedPartLinear1_18 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart1_18 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart1_18]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart1_18]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1
def selectedPartLinear1_19 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart1_19 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart1_19]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart1_19]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1
def selectedPartLinear1_20 (X Y Z W a b : ℂ) (i:ℕ) : (Fin 210→ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => selectedPart1_20 X Y Z W a b v i
  map_add' := by
    intro v w
    dsimp only [selectedPart1_20]
    split <;> simp only [Pi.add_apply,mul_add] <;> ring1
  map_smul' := by
    intro c v
    dsimp only [selectedPart1_20]
    split <;> simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring1

end QuantitativeArithmeticSmallLevelThirtyFiveFullGrid
end
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveFullGridCaseIndexSignGaugePartsBundleSeriesV4 -/
section
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 0
set_option maxRecDepth 4000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyFiveFullGrid

theorem part2_0_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart2_0 X Y Z W a b v i = selectedPart1_0 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart2_0,selectedPart1_0] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part2_0_sign_change
theorem part2_1_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart2_1 X Y Z W a b v i = selectedPart1_1 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart2_1,selectedPart1_1] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part2_1_sign_change
theorem part2_2_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart2_2 X Y Z W a b v i = selectedPart1_2 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart2_2,selectedPart1_2] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part2_2_sign_change

theorem part2_3_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart2_3 X Y Z W a b v i = selectedPart1_3 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart2_3,selectedPart1_3] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part2_3_sign_change
theorem part2_4_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart2_4 X Y Z W a b v i = selectedPart1_4 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart2_4,selectedPart1_4] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part2_4_sign_change
theorem part2_5_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart2_5 X Y Z W a b v i = selectedPart1_5 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart2_5,selectedPart1_5] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part2_5_sign_change

theorem part2_6_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart2_6 X Y Z W a b v i = selectedPart1_6 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart2_6,selectedPart1_6] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part2_6_sign_change
theorem part2_7_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart2_7 X Y Z W a b v i = selectedPart1_7 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart2_7,selectedPart1_7] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part2_7_sign_change
theorem part2_8_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart2_8 X Y Z W a b v i = selectedPart1_8 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart2_8,selectedPart1_8] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part2_8_sign_change

theorem part2_9_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart2_9 X Y Z W a b v i = selectedPart1_9 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart2_9,selectedPart1_9] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part2_9_sign_change
theorem part2_10_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart2_10 X Y Z W a b v i = selectedPart1_10 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart2_10,selectedPart1_10] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part2_10_sign_change
theorem part2_11_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart2_11 X Y Z W a b v i = selectedPart1_11 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart2_11,selectedPart1_11] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part2_11_sign_change

theorem part2_12_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart2_12 X Y Z W a b v i = selectedPart1_12 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart2_12,selectedPart1_12] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part2_12_sign_change
theorem part2_13_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart2_13 X Y Z W a b v i = selectedPart1_13 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart2_13,selectedPart1_13] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part2_13_sign_change
theorem part2_14_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart2_14 X Y Z W a b v i = selectedPart1_14 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart2_14,selectedPart1_14] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part2_14_sign_change

theorem part2_15_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart2_15 X Y Z W a b v i = selectedPart1_15 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart2_15,selectedPart1_15] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part2_15_sign_change
theorem part2_16_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart2_16 X Y Z W a b v i = selectedPart1_16 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart2_16,selectedPart1_16] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part2_16_sign_change
theorem part2_17_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart2_17 X Y Z W a b v i = selectedPart1_17 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart2_17,selectedPart1_17] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part2_17_sign_change

theorem part2_18_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart2_18 X Y Z W a b v i = selectedPart1_18 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart2_18,selectedPart1_18] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part2_18_sign_change
theorem part2_19_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart2_19 X Y Z W a b v i = selectedPart1_19 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart2_19,selectedPart1_19] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part2_19_sign_change
theorem part2_20_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart2_20 X Y Z W a b v i = selectedPart1_20 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart2_20,selectedPart1_20] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part2_20_sign_change

end QuantitativeArithmeticSmallLevelThirtyFiveFullGrid
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 0
set_option maxRecDepth 4000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyFiveFullGrid

theorem part3_0_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart3_0 X Y Z W a b v i = selectedPart0_0 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart3_0,selectedPart0_0] <;>
    split <;> (
    field_simp [hX,hY,hZ,hW]
    all_goals ring_nf
    all_goals field_simp [hX,hY,hZ,hW]
    all_goals ring1)
#print axioms part3_0_sign_change
theorem part3_1_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart3_1 X Y Z W a b v i = selectedPart0_1 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart3_1,selectedPart0_1] <;>
    split <;> (
    field_simp [hX,hY,hZ,hW]
    all_goals ring_nf
    all_goals field_simp [hX,hY,hZ,hW]
    all_goals ring1)
#print axioms part3_1_sign_change
theorem part3_2_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart3_2 X Y Z W a b v i = selectedPart0_2 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart3_2,selectedPart0_2] <;>
    split <;> (
    field_simp [hX,hY,hZ,hW]
    all_goals ring_nf
    all_goals field_simp [hX,hY,hZ,hW]
    all_goals ring1)
#print axioms part3_2_sign_change

theorem part3_3_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart3_3 X Y Z W a b v i = selectedPart0_3 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart3_3,selectedPart0_3] <;>
    split <;> (
    field_simp [hX,hY,hZ,hW]
    all_goals ring_nf
    all_goals field_simp [hX,hY,hZ,hW]
    all_goals ring1)
#print axioms part3_3_sign_change
theorem part3_4_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart3_4 X Y Z W a b v i = selectedPart0_4 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart3_4,selectedPart0_4] <;>
    split <;> (
    field_simp [hX,hY,hZ,hW]
    all_goals ring_nf
    all_goals field_simp [hX,hY,hZ,hW]
    all_goals ring1)
#print axioms part3_4_sign_change
theorem part3_5_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart3_5 X Y Z W a b v i = selectedPart0_5 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart3_5,selectedPart0_5] <;>
    split <;> (
    field_simp [hX,hY,hZ,hW]
    all_goals ring_nf
    all_goals field_simp [hX,hY,hZ,hW]
    all_goals ring1)
#print axioms part3_5_sign_change

theorem part3_6_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart3_6 X Y Z W a b v i = selectedPart0_6 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart3_6,selectedPart0_6] <;>
    split <;> (
    field_simp [hX,hY,hZ,hW]
    all_goals ring_nf
    all_goals field_simp [hX,hY,hZ,hW]
    all_goals ring1)
#print axioms part3_6_sign_change
theorem part3_7_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart3_7 X Y Z W a b v i = selectedPart0_7 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart3_7,selectedPart0_7] <;>
    split <;> (
    field_simp [hX,hY,hZ,hW]
    all_goals ring_nf
    all_goals field_simp [hX,hY,hZ,hW]
    all_goals ring1)
#print axioms part3_7_sign_change
theorem part3_8_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart3_8 X Y Z W a b v i = selectedPart0_8 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart3_8,selectedPart0_8] <;>
    split <;> (
    field_simp [hX,hY,hZ,hW]
    all_goals ring_nf
    all_goals field_simp [hX,hY,hZ,hW]
    all_goals ring1)
#print axioms part3_8_sign_change

theorem part3_9_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart3_9 X Y Z W a b v i = selectedPart0_9 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart3_9,selectedPart0_9] <;>
    split <;> (
    field_simp [hX,hY,hZ,hW]
    all_goals ring_nf
    all_goals field_simp [hX,hY,hZ,hW]
    all_goals ring1)
#print axioms part3_9_sign_change
theorem part3_10_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart3_10 X Y Z W a b v i = selectedPart0_10 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart3_10,selectedPart0_10] <;>
    split <;> (
    field_simp [hX,hY,hZ,hW]
    all_goals ring_nf
    all_goals field_simp [hX,hY,hZ,hW]
    all_goals ring1)
#print axioms part3_10_sign_change
theorem part3_11_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart3_11 X Y Z W a b v i = selectedPart0_11 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart3_11,selectedPart0_11] <;>
    split <;> (
    field_simp [hX,hY,hZ,hW]
    all_goals ring_nf
    all_goals field_simp [hX,hY,hZ,hW]
    all_goals ring1)
#print axioms part3_11_sign_change

theorem part3_12_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart3_12 X Y Z W a b v i = selectedPart0_12 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart3_12,selectedPart0_12] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part3_12_sign_change
theorem part3_13_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart3_13 X Y Z W a b v i = selectedPart0_13 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart3_13,selectedPart0_13] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part3_13_sign_change
theorem part3_14_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart3_14 X Y Z W a b v i = selectedPart0_14 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart3_14,selectedPart0_14] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part3_14_sign_change

theorem part3_15_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart3_15 X Y Z W a b v i = selectedPart0_15 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart3_15,selectedPart0_15] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part3_15_sign_change
theorem part3_16_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart3_16 X Y Z W a b v i = selectedPart0_16 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart3_16,selectedPart0_16] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part3_16_sign_change
theorem part3_17_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart3_17 X Y Z W a b v i = selectedPart0_17 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart3_17,selectedPart0_17] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part3_17_sign_change

theorem part3_18_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart3_18 X Y Z W a b v i = selectedPart0_18 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart3_18,selectedPart0_18] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part3_18_sign_change
theorem part3_19_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart3_19 X Y Z W a b v i = selectedPart0_19 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart3_19,selectedPart0_19] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part3_19_sign_change
theorem part3_20_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart3_20 X Y Z W a b v i = selectedPart0_20 X Y (-Z) (-W) a b v i := by
  dsimp only [selectedPart3_20,selectedPart0_20] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part3_20_sign_change

end QuantitativeArithmeticSmallLevelThirtyFiveFullGrid
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 0
set_option maxRecDepth 4000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyFiveFullGrid

theorem part4_0_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart4_0 X Y Z W a b v i = selectedPart1_0 X Y Z (-W) a b v i := by
  dsimp only [selectedPart4_0,selectedPart1_0] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part4_0_sign_change
theorem part4_1_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart4_1 X Y Z W a b v i = selectedPart1_1 X Y Z (-W) a b v i := by
  dsimp only [selectedPart4_1,selectedPart1_1] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part4_1_sign_change
theorem part4_2_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart4_2 X Y Z W a b v i = selectedPart1_2 X Y Z (-W) a b v i := by
  dsimp only [selectedPart4_2,selectedPart1_2] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part4_2_sign_change

theorem part4_3_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart4_3 X Y Z W a b v i = selectedPart1_3 X Y Z (-W) a b v i := by
  dsimp only [selectedPart4_3,selectedPart1_3] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part4_3_sign_change
theorem part4_4_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart4_4 X Y Z W a b v i = selectedPart1_4 X Y Z (-W) a b v i := by
  dsimp only [selectedPart4_4,selectedPart1_4] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part4_4_sign_change
theorem part4_5_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart4_5 X Y Z W a b v i = selectedPart1_5 X Y Z (-W) a b v i := by
  dsimp only [selectedPart4_5,selectedPart1_5] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part4_5_sign_change

theorem part4_6_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart4_6 X Y Z W a b v i = selectedPart1_6 X Y Z (-W) a b v i := by
  dsimp only [selectedPart4_6,selectedPart1_6] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part4_6_sign_change
theorem part4_7_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart4_7 X Y Z W a b v i = selectedPart1_7 X Y Z (-W) a b v i := by
  dsimp only [selectedPart4_7,selectedPart1_7] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part4_7_sign_change
theorem part4_8_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart4_8 X Y Z W a b v i = selectedPart1_8 X Y Z (-W) a b v i := by
  dsimp only [selectedPart4_8,selectedPart1_8] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part4_8_sign_change

theorem part4_9_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart4_9 X Y Z W a b v i = selectedPart1_9 X Y Z (-W) a b v i := by
  dsimp only [selectedPart4_9,selectedPart1_9] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part4_9_sign_change
theorem part4_10_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart4_10 X Y Z W a b v i = selectedPart1_10 X Y Z (-W) a b v i := by
  dsimp only [selectedPart4_10,selectedPart1_10] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part4_10_sign_change
theorem part4_11_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart4_11 X Y Z W a b v i = selectedPart1_11 X Y Z (-W) a b v i := by
  dsimp only [selectedPart4_11,selectedPart1_11] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part4_11_sign_change

theorem part4_12_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart4_12 X Y Z W a b v i = selectedPart1_12 X Y Z (-W) a b v i := by
  dsimp only [selectedPart4_12,selectedPart1_12] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part4_12_sign_change
theorem part4_13_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart4_13 X Y Z W a b v i = selectedPart1_13 X Y Z (-W) a b v i := by
  dsimp only [selectedPart4_13,selectedPart1_13] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part4_13_sign_change
theorem part4_14_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart4_14 X Y Z W a b v i = selectedPart1_14 X Y Z (-W) a b v i := by
  dsimp only [selectedPart4_14,selectedPart1_14] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part4_14_sign_change

theorem part4_15_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart4_15 X Y Z W a b v i = selectedPart1_15 X Y Z (-W) a b v i := by
  dsimp only [selectedPart4_15,selectedPart1_15] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part4_15_sign_change
theorem part4_16_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart4_16 X Y Z W a b v i = selectedPart1_16 X Y Z (-W) a b v i := by
  dsimp only [selectedPart4_16,selectedPart1_16] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part4_16_sign_change
theorem part4_17_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart4_17 X Y Z W a b v i = selectedPart1_17 X Y Z (-W) a b v i := by
  dsimp only [selectedPart4_17,selectedPart1_17] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part4_17_sign_change

theorem part4_18_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart4_18 X Y Z W a b v i = selectedPart1_18 X Y Z (-W) a b v i := by
  dsimp only [selectedPart4_18,selectedPart1_18] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part4_18_sign_change
theorem part4_19_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart4_19 X Y Z W a b v i = selectedPart1_19 X Y Z (-W) a b v i := by
  dsimp only [selectedPart4_19,selectedPart1_19] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part4_19_sign_change
theorem part4_20_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart4_20 X Y Z W a b v i = selectedPart1_20 X Y Z (-W) a b v i := by
  dsimp only [selectedPart4_20,selectedPart1_20] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part4_20_sign_change

end QuantitativeArithmeticSmallLevelThirtyFiveFullGrid
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 0
set_option maxRecDepth 4000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyFiveFullGrid

theorem part5_0_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart5_0 X Y Z W a b v i = selectedPart0_0 X Y Z (-W) a b v i := by
  dsimp only [selectedPart5_0,selectedPart0_0] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part5_0_sign_change
theorem part5_1_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart5_1 X Y Z W a b v i = selectedPart0_1 X Y Z (-W) a b v i := by
  dsimp only [selectedPart5_1,selectedPart0_1] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part5_1_sign_change
theorem part5_2_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart5_2 X Y Z W a b v i = selectedPart0_2 X Y Z (-W) a b v i := by
  dsimp only [selectedPart5_2,selectedPart0_2] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part5_2_sign_change

theorem part5_3_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart5_3 X Y Z W a b v i = selectedPart0_3 X Y Z (-W) a b v i := by
  dsimp only [selectedPart5_3,selectedPart0_3] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part5_3_sign_change
theorem part5_4_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart5_4 X Y Z W a b v i = selectedPart0_4 X Y Z (-W) a b v i := by
  dsimp only [selectedPart5_4,selectedPart0_4] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part5_4_sign_change
theorem part5_5_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart5_5 X Y Z W a b v i = selectedPart0_5 X Y Z (-W) a b v i := by
  dsimp only [selectedPart5_5,selectedPart0_5] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part5_5_sign_change

theorem part5_6_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart5_6 X Y Z W a b v i = selectedPart0_6 X Y Z (-W) a b v i := by
  dsimp only [selectedPart5_6,selectedPart0_6] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part5_6_sign_change
theorem part5_7_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart5_7 X Y Z W a b v i = selectedPart0_7 X Y Z (-W) a b v i := by
  dsimp only [selectedPart5_7,selectedPart0_7] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part5_7_sign_change
theorem part5_8_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart5_8 X Y Z W a b v i = selectedPart0_8 X Y Z (-W) a b v i := by
  dsimp only [selectedPart5_8,selectedPart0_8] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part5_8_sign_change

theorem part5_9_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart5_9 X Y Z W a b v i = selectedPart0_9 X Y Z (-W) a b v i := by
  dsimp only [selectedPart5_9,selectedPart0_9] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part5_9_sign_change
theorem part5_10_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart5_10 X Y Z W a b v i = selectedPart0_10 X Y Z (-W) a b v i := by
  dsimp only [selectedPart5_10,selectedPart0_10] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part5_10_sign_change
theorem part5_11_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart5_11 X Y Z W a b v i = selectedPart0_11 X Y Z (-W) a b v i := by
  dsimp only [selectedPart5_11,selectedPart0_11] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part5_11_sign_change

theorem part5_12_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart5_12 X Y Z W a b v i = selectedPart0_12 X Y Z (-W) a b v i := by
  dsimp only [selectedPart5_12,selectedPart0_12] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part5_12_sign_change
theorem part5_13_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart5_13 X Y Z W a b v i = selectedPart0_13 X Y Z (-W) a b v i := by
  dsimp only [selectedPart5_13,selectedPart0_13] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part5_13_sign_change
theorem part5_14_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart5_14 X Y Z W a b v i = selectedPart0_14 X Y Z (-W) a b v i := by
  dsimp only [selectedPart5_14,selectedPart0_14] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part5_14_sign_change

theorem part5_15_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart5_15 X Y Z W a b v i = selectedPart0_15 X Y Z (-W) a b v i := by
  dsimp only [selectedPart5_15,selectedPart0_15] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part5_15_sign_change
theorem part5_16_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart5_16 X Y Z W a b v i = selectedPart0_16 X Y Z (-W) a b v i := by
  dsimp only [selectedPart5_16,selectedPart0_16] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part5_16_sign_change
theorem part5_17_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart5_17 X Y Z W a b v i = selectedPart0_17 X Y Z (-W) a b v i := by
  dsimp only [selectedPart5_17,selectedPart0_17] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part5_17_sign_change

theorem part5_18_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart5_18 X Y Z W a b v i = selectedPart0_18 X Y Z (-W) a b v i := by
  dsimp only [selectedPart5_18,selectedPart0_18] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part5_18_sign_change
theorem part5_19_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart5_19 X Y Z W a b v i = selectedPart0_19 X Y Z (-W) a b v i := by
  dsimp only [selectedPart5_19,selectedPart0_19] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part5_19_sign_change
theorem part5_20_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart5_20 X Y Z W a b v i = selectedPart0_20 X Y Z (-W) a b v i := by
  dsimp only [selectedPart5_20,selectedPart0_20] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part5_20_sign_change

end QuantitativeArithmeticSmallLevelThirtyFiveFullGrid
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 0
set_option maxRecDepth 4000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyFiveFullGrid

theorem part6_0_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart6_0 X Y Z W a b v i = selectedPart0_0 X Y (-Z) W a b v i := by
  dsimp only [selectedPart6_0,selectedPart0_0] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part6_0_sign_change
theorem part6_1_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart6_1 X Y Z W a b v i = selectedPart0_1 X Y (-Z) W a b v i := by
  dsimp only [selectedPart6_1,selectedPart0_1] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part6_1_sign_change
theorem part6_2_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart6_2 X Y Z W a b v i = selectedPart0_2 X Y (-Z) W a b v i := by
  dsimp only [selectedPart6_2,selectedPart0_2] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part6_2_sign_change

theorem part6_3_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart6_3 X Y Z W a b v i = selectedPart0_3 X Y (-Z) W a b v i := by
  dsimp only [selectedPart6_3,selectedPart0_3] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part6_3_sign_change
theorem part6_4_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart6_4 X Y Z W a b v i = selectedPart0_4 X Y (-Z) W a b v i := by
  dsimp only [selectedPart6_4,selectedPart0_4] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part6_4_sign_change
theorem part6_5_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart6_5 X Y Z W a b v i = selectedPart0_5 X Y (-Z) W a b v i := by
  dsimp only [selectedPart6_5,selectedPart0_5] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part6_5_sign_change

theorem part6_6_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart6_6 X Y Z W a b v i = selectedPart0_6 X Y (-Z) W a b v i := by
  dsimp only [selectedPart6_6,selectedPart0_6] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part6_6_sign_change
theorem part6_7_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart6_7 X Y Z W a b v i = selectedPart0_7 X Y (-Z) W a b v i := by
  dsimp only [selectedPart6_7,selectedPart0_7] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part6_7_sign_change
theorem part6_8_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart6_8 X Y Z W a b v i = selectedPart0_8 X Y (-Z) W a b v i := by
  dsimp only [selectedPart6_8,selectedPart0_8] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part6_8_sign_change

theorem part6_9_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart6_9 X Y Z W a b v i = selectedPart0_9 X Y (-Z) W a b v i := by
  dsimp only [selectedPart6_9,selectedPart0_9] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part6_9_sign_change
theorem part6_10_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart6_10 X Y Z W a b v i = selectedPart0_10 X Y (-Z) W a b v i := by
  dsimp only [selectedPart6_10,selectedPart0_10] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part6_10_sign_change
theorem part6_11_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart6_11 X Y Z W a b v i = selectedPart0_11 X Y (-Z) W a b v i := by
  dsimp only [selectedPart6_11,selectedPart0_11] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part6_11_sign_change

theorem part6_12_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart6_12 X Y Z W a b v i = selectedPart0_12 X Y (-Z) W a b v i := by
  dsimp only [selectedPart6_12,selectedPart0_12] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part6_12_sign_change
theorem part6_13_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart6_13 X Y Z W a b v i = selectedPart0_13 X Y (-Z) W a b v i := by
  dsimp only [selectedPart6_13,selectedPart0_13] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part6_13_sign_change
theorem part6_14_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart6_14 X Y Z W a b v i = selectedPart0_14 X Y (-Z) W a b v i := by
  dsimp only [selectedPart6_14,selectedPart0_14] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part6_14_sign_change

theorem part6_15_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart6_15 X Y Z W a b v i = selectedPart0_15 X Y (-Z) W a b v i := by
  dsimp only [selectedPart6_15,selectedPart0_15] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part6_15_sign_change
theorem part6_16_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart6_16 X Y Z W a b v i = selectedPart0_16 X Y (-Z) W a b v i := by
  dsimp only [selectedPart6_16,selectedPart0_16] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part6_16_sign_change
theorem part6_17_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart6_17 X Y Z W a b v i = selectedPart0_17 X Y (-Z) W a b v i := by
  dsimp only [selectedPart6_17,selectedPart0_17] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part6_17_sign_change

theorem part6_18_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart6_18 X Y Z W a b v i = selectedPart0_18 X Y (-Z) W a b v i := by
  dsimp only [selectedPart6_18,selectedPart0_18] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part6_18_sign_change
theorem part6_19_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart6_19 X Y Z W a b v i = selectedPart0_19 X Y (-Z) W a b v i := by
  dsimp only [selectedPart6_19,selectedPart0_19] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part6_19_sign_change
theorem part6_20_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart6_20 X Y Z W a b v i = selectedPart0_20 X Y (-Z) W a b v i := by
  dsimp only [selectedPart6_20,selectedPart0_20] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part6_20_sign_change

end QuantitativeArithmeticSmallLevelThirtyFiveFullGrid
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 0
set_option maxRecDepth 4000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyFiveFullGrid

theorem part7_0_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart7_0 X Y Z W a b v i = selectedPart1_0 X Y (-Z) W a b v i := by
  dsimp only [selectedPart7_0,selectedPart1_0] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part7_0_sign_change
theorem part7_1_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart7_1 X Y Z W a b v i = selectedPart1_1 X Y (-Z) W a b v i := by
  dsimp only [selectedPart7_1,selectedPart1_1] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part7_1_sign_change
theorem part7_2_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart7_2 X Y Z W a b v i = selectedPart1_2 X Y (-Z) W a b v i := by
  dsimp only [selectedPart7_2,selectedPart1_2] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part7_2_sign_change

theorem part7_3_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart7_3 X Y Z W a b v i = selectedPart1_3 X Y (-Z) W a b v i := by
  dsimp only [selectedPart7_3,selectedPart1_3] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part7_3_sign_change
theorem part7_4_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart7_4 X Y Z W a b v i = selectedPart1_4 X Y (-Z) W a b v i := by
  dsimp only [selectedPart7_4,selectedPart1_4] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part7_4_sign_change
theorem part7_5_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart7_5 X Y Z W a b v i = selectedPart1_5 X Y (-Z) W a b v i := by
  dsimp only [selectedPart7_5,selectedPart1_5] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part7_5_sign_change

theorem part7_6_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart7_6 X Y Z W a b v i = selectedPart1_6 X Y (-Z) W a b v i := by
  dsimp only [selectedPart7_6,selectedPart1_6] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part7_6_sign_change
theorem part7_7_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart7_7 X Y Z W a b v i = selectedPart1_7 X Y (-Z) W a b v i := by
  dsimp only [selectedPart7_7,selectedPart1_7] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part7_7_sign_change
theorem part7_8_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart7_8 X Y Z W a b v i = selectedPart1_8 X Y (-Z) W a b v i := by
  dsimp only [selectedPart7_8,selectedPart1_8] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part7_8_sign_change

theorem part7_9_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart7_9 X Y Z W a b v i = selectedPart1_9 X Y (-Z) W a b v i := by
  dsimp only [selectedPart7_9,selectedPart1_9] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part7_9_sign_change
theorem part7_10_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart7_10 X Y Z W a b v i = selectedPart1_10 X Y (-Z) W a b v i := by
  dsimp only [selectedPart7_10,selectedPart1_10] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part7_10_sign_change
theorem part7_11_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart7_11 X Y Z W a b v i = selectedPart1_11 X Y (-Z) W a b v i := by
  dsimp only [selectedPart7_11,selectedPart1_11] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part7_11_sign_change

theorem part7_12_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart7_12 X Y Z W a b v i = selectedPart1_12 X Y (-Z) W a b v i := by
  dsimp only [selectedPart7_12,selectedPart1_12] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part7_12_sign_change
theorem part7_13_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart7_13 X Y Z W a b v i = selectedPart1_13 X Y (-Z) W a b v i := by
  dsimp only [selectedPart7_13,selectedPart1_13] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part7_13_sign_change
theorem part7_14_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart7_14 X Y Z W a b v i = selectedPart1_14 X Y (-Z) W a b v i := by
  dsimp only [selectedPart7_14,selectedPart1_14] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part7_14_sign_change

theorem part7_15_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart7_15 X Y Z W a b v i = selectedPart1_15 X Y (-Z) W a b v i := by
  dsimp only [selectedPart7_15,selectedPart1_15] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part7_15_sign_change
theorem part7_16_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart7_16 X Y Z W a b v i = selectedPart1_16 X Y (-Z) W a b v i := by
  dsimp only [selectedPart7_16,selectedPart1_16] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part7_16_sign_change
theorem part7_17_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart7_17 X Y Z W a b v i = selectedPart1_17 X Y (-Z) W a b v i := by
  dsimp only [selectedPart7_17,selectedPart1_17] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part7_17_sign_change

theorem part7_18_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart7_18 X Y Z W a b v i = selectedPart1_18 X Y (-Z) W a b v i := by
  dsimp only [selectedPart7_18,selectedPart1_18] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part7_18_sign_change
theorem part7_19_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart7_19 X Y Z W a b v i = selectedPart1_19 X Y (-Z) W a b v i := by
  dsimp only [selectedPart7_19,selectedPart1_19] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part7_19_sign_change
theorem part7_20_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) (i:ℕ) :
    selectedPart7_20 X Y Z W a b v i = selectedPart1_20 X Y (-Z) W a b v i := by
  dsimp only [selectedPart7_20,selectedPart1_20] <;>
    split <;> simp only [neg_one_mul, mul_neg, neg_mul, div_neg, neg_div,
    neg_neg, neg_sq, one_mul]
#print axioms part7_20_sign_change

end QuantitativeArithmeticSmallLevelThirtyFiveFullGrid
end
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveFullGridCaseIndexSignGaugeSeriesV4 -/
section
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option maxRecDepth 4000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace QuantitativeArithmeticSmallLevelThirtyFiveFullGrid
theorem rows2_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) :
    selectedRowsV3_2 X Y Z W a b v = selectedRowsV3_1 X Y (-Z) (-W) a b v := by
  funext i
  dsimp only [selectedRowsV3_2,selectedRowsV3_1]
  split <;> simp_all only [part2_0_sign_change X Y Z W a b hX hY hZ hW v,
    part2_1_sign_change X Y Z W a b hX hY hZ hW v,
    part2_2_sign_change X Y Z W a b hX hY hZ hW v,
    part2_3_sign_change X Y Z W a b hX hY hZ hW v,
    part2_4_sign_change X Y Z W a b hX hY hZ hW v,
    part2_5_sign_change X Y Z W a b hX hY hZ hW v,
    part2_6_sign_change X Y Z W a b hX hY hZ hW v,
    part2_7_sign_change X Y Z W a b hX hY hZ hW v,
    part2_8_sign_change X Y Z W a b hX hY hZ hW v,
    part2_9_sign_change X Y Z W a b hX hY hZ hW v,
    part2_10_sign_change X Y Z W a b hX hY hZ hW v,
    part2_11_sign_change X Y Z W a b hX hY hZ hW v,
    part2_12_sign_change X Y Z W a b hX hY hZ hW v,
    part2_13_sign_change X Y Z W a b hX hY hZ hW v,
    part2_14_sign_change X Y Z W a b hX hY hZ hW v,
    part2_15_sign_change X Y Z W a b hX hY hZ hW v,
    part2_16_sign_change X Y Z W a b hX hY hZ hW v,
    part2_17_sign_change X Y Z W a b hX hY hZ hW v,
    part2_18_sign_change X Y Z W a b hX hY hZ hW v,
    part2_19_sign_change X Y Z W a b hX hY hZ hW v,
    part2_20_sign_change X Y Z W a b hX hY hZ hW v]
#print axioms rows2_sign_change


theorem rows3_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) :
    selectedRowsV3_3 X Y Z W a b v = selectedRowsV3_0 X Y (-Z) (-W) a b v := by
  funext i
  dsimp only [selectedRowsV3_3,selectedRowsV3_0]
  split <;> simp_all only [part3_0_sign_change X Y Z W a b hX hY hZ hW v,
    part3_1_sign_change X Y Z W a b hX hY hZ hW v,
    part3_2_sign_change X Y Z W a b hX hY hZ hW v,
    part3_3_sign_change X Y Z W a b hX hY hZ hW v,
    part3_4_sign_change X Y Z W a b hX hY hZ hW v,
    part3_5_sign_change X Y Z W a b hX hY hZ hW v,
    part3_6_sign_change X Y Z W a b hX hY hZ hW v,
    part3_7_sign_change X Y Z W a b hX hY hZ hW v,
    part3_8_sign_change X Y Z W a b hX hY hZ hW v,
    part3_9_sign_change X Y Z W a b hX hY hZ hW v,
    part3_10_sign_change X Y Z W a b hX hY hZ hW v,
    part3_11_sign_change X Y Z W a b hX hY hZ hW v,
    part3_12_sign_change X Y Z W a b hX hY hZ hW v,
    part3_13_sign_change X Y Z W a b hX hY hZ hW v,
    part3_14_sign_change X Y Z W a b hX hY hZ hW v,
    part3_15_sign_change X Y Z W a b hX hY hZ hW v,
    part3_16_sign_change X Y Z W a b hX hY hZ hW v,
    part3_17_sign_change X Y Z W a b hX hY hZ hW v,
    part3_18_sign_change X Y Z W a b hX hY hZ hW v,
    part3_19_sign_change X Y Z W a b hX hY hZ hW v,
    part3_20_sign_change X Y Z W a b hX hY hZ hW v]
#print axioms rows3_sign_change


theorem rows4_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) :
    selectedRowsV3_4 X Y Z W a b v = selectedRowsV3_1 X Y Z (-W) a b v := by
  funext i
  dsimp only [selectedRowsV3_4,selectedRowsV3_1]
  split <;> simp_all only [part4_0_sign_change X Y Z W a b hX hY hZ hW v,
    part4_1_sign_change X Y Z W a b hX hY hZ hW v,
    part4_2_sign_change X Y Z W a b hX hY hZ hW v,
    part4_3_sign_change X Y Z W a b hX hY hZ hW v,
    part4_4_sign_change X Y Z W a b hX hY hZ hW v,
    part4_5_sign_change X Y Z W a b hX hY hZ hW v,
    part4_6_sign_change X Y Z W a b hX hY hZ hW v,
    part4_7_sign_change X Y Z W a b hX hY hZ hW v,
    part4_8_sign_change X Y Z W a b hX hY hZ hW v,
    part4_9_sign_change X Y Z W a b hX hY hZ hW v,
    part4_10_sign_change X Y Z W a b hX hY hZ hW v,
    part4_11_sign_change X Y Z W a b hX hY hZ hW v,
    part4_12_sign_change X Y Z W a b hX hY hZ hW v,
    part4_13_sign_change X Y Z W a b hX hY hZ hW v,
    part4_14_sign_change X Y Z W a b hX hY hZ hW v,
    part4_15_sign_change X Y Z W a b hX hY hZ hW v,
    part4_16_sign_change X Y Z W a b hX hY hZ hW v,
    part4_17_sign_change X Y Z W a b hX hY hZ hW v,
    part4_18_sign_change X Y Z W a b hX hY hZ hW v,
    part4_19_sign_change X Y Z W a b hX hY hZ hW v,
    part4_20_sign_change X Y Z W a b hX hY hZ hW v]
#print axioms rows4_sign_change


theorem rows5_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) :
    selectedRowsV3_5 X Y Z W a b v = selectedRowsV3_0 X Y Z (-W) a b v := by
  funext i
  dsimp only [selectedRowsV3_5,selectedRowsV3_0]
  split <;> simp_all only [part5_0_sign_change X Y Z W a b hX hY hZ hW v,
    part5_1_sign_change X Y Z W a b hX hY hZ hW v,
    part5_2_sign_change X Y Z W a b hX hY hZ hW v,
    part5_3_sign_change X Y Z W a b hX hY hZ hW v,
    part5_4_sign_change X Y Z W a b hX hY hZ hW v,
    part5_5_sign_change X Y Z W a b hX hY hZ hW v,
    part5_6_sign_change X Y Z W a b hX hY hZ hW v,
    part5_7_sign_change X Y Z W a b hX hY hZ hW v,
    part5_8_sign_change X Y Z W a b hX hY hZ hW v,
    part5_9_sign_change X Y Z W a b hX hY hZ hW v,
    part5_10_sign_change X Y Z W a b hX hY hZ hW v,
    part5_11_sign_change X Y Z W a b hX hY hZ hW v,
    part5_12_sign_change X Y Z W a b hX hY hZ hW v,
    part5_13_sign_change X Y Z W a b hX hY hZ hW v,
    part5_14_sign_change X Y Z W a b hX hY hZ hW v,
    part5_15_sign_change X Y Z W a b hX hY hZ hW v,
    part5_16_sign_change X Y Z W a b hX hY hZ hW v,
    part5_17_sign_change X Y Z W a b hX hY hZ hW v,
    part5_18_sign_change X Y Z W a b hX hY hZ hW v,
    part5_19_sign_change X Y Z W a b hX hY hZ hW v,
    part5_20_sign_change X Y Z W a b hX hY hZ hW v]
#print axioms rows5_sign_change


theorem rows6_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) :
    selectedRowsV3_6 X Y Z W a b v = selectedRowsV3_0 X Y (-Z) W a b v := by
  funext i
  dsimp only [selectedRowsV3_6,selectedRowsV3_0]
  split <;> simp_all only [part6_0_sign_change X Y Z W a b hX hY hZ hW v,
    part6_1_sign_change X Y Z W a b hX hY hZ hW v,
    part6_2_sign_change X Y Z W a b hX hY hZ hW v,
    part6_3_sign_change X Y Z W a b hX hY hZ hW v,
    part6_4_sign_change X Y Z W a b hX hY hZ hW v,
    part6_5_sign_change X Y Z W a b hX hY hZ hW v,
    part6_6_sign_change X Y Z W a b hX hY hZ hW v,
    part6_7_sign_change X Y Z W a b hX hY hZ hW v,
    part6_8_sign_change X Y Z W a b hX hY hZ hW v,
    part6_9_sign_change X Y Z W a b hX hY hZ hW v,
    part6_10_sign_change X Y Z W a b hX hY hZ hW v,
    part6_11_sign_change X Y Z W a b hX hY hZ hW v,
    part6_12_sign_change X Y Z W a b hX hY hZ hW v,
    part6_13_sign_change X Y Z W a b hX hY hZ hW v,
    part6_14_sign_change X Y Z W a b hX hY hZ hW v,
    part6_15_sign_change X Y Z W a b hX hY hZ hW v,
    part6_16_sign_change X Y Z W a b hX hY hZ hW v,
    part6_17_sign_change X Y Z W a b hX hY hZ hW v,
    part6_18_sign_change X Y Z W a b hX hY hZ hW v,
    part6_19_sign_change X Y Z W a b hX hY hZ hW v,
    part6_20_sign_change X Y Z W a b hX hY hZ hW v]
#print axioms rows6_sign_change


theorem rows7_sign_change (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) :
    selectedRowsV3_7 X Y Z W a b v = selectedRowsV3_1 X Y (-Z) W a b v := by
  funext i
  dsimp only [selectedRowsV3_7,selectedRowsV3_1]
  split <;> simp_all only [part7_0_sign_change X Y Z W a b hX hY hZ hW v,
    part7_1_sign_change X Y Z W a b hX hY hZ hW v,
    part7_2_sign_change X Y Z W a b hX hY hZ hW v,
    part7_3_sign_change X Y Z W a b hX hY hZ hW v,
    part7_4_sign_change X Y Z W a b hX hY hZ hW v,
    part7_5_sign_change X Y Z W a b hX hY hZ hW v,
    part7_6_sign_change X Y Z W a b hX hY hZ hW v,
    part7_7_sign_change X Y Z W a b hX hY hZ hW v,
    part7_8_sign_change X Y Z W a b hX hY hZ hW v,
    part7_9_sign_change X Y Z W a b hX hY hZ hW v,
    part7_10_sign_change X Y Z W a b hX hY hZ hW v,
    part7_11_sign_change X Y Z W a b hX hY hZ hW v,
    part7_12_sign_change X Y Z W a b hX hY hZ hW v,
    part7_13_sign_change X Y Z W a b hX hY hZ hW v,
    part7_14_sign_change X Y Z W a b hX hY hZ hW v,
    part7_15_sign_change X Y Z W a b hX hY hZ hW v,
    part7_16_sign_change X Y Z W a b hX hY hZ hW v,
    part7_17_sign_change X Y Z W a b hX hY hZ hW v,
    part7_18_sign_change X Y Z W a b hX hY hZ hW v,
    part7_19_sign_change X Y Z W a b hX hY hZ hW v,
    part7_20_sign_change X Y Z W a b hX hY hZ hW v]
#print axioms rows7_sign_change

end QuantitativeArithmeticSmallLevelThirtyFiveFullGrid
end
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveFullGridCaseIndexGaugeKernelSeriesV4 -/
section
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option maxRecDepth 4000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace QuantitativeArithmeticSmallLevelThirtyFiveFullGrid
theorem selected_kernel_gauge_case2 (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (hD0 : (X^2*Y^2 + X*Y^2*a + Y^2)≠0)
    (hD1 : ((2)*X^2 + (2)*X*a + (2))≠0)
    (hD2 : (X^4 + X*a + (-1)*Y*b + (-1))≠0)
    (hD3 : (Y^2 + Y*b + (5))≠0)
    (hD4 : (X^2 + X*a)≠0)
    (hD5 : (X + a)≠0)
    (hD6 : (X^4 + X^3*a)≠0)
    (hD7 : (X^3 + X^2*a)≠0)
    (hD8 : (X^6 + X^5*a)≠0)
    (hD9 : (X^5 + X^4*a)≠0)
    (hD10 : (X^6 + X^5*a + X^4*a^2 + (2)*X^3*a + X^2*a^2 + X*a + (1))≠0)
    (v:Fin 210→ℂ) (hv:selectedRowsV3_2 X Y Z W a b v=0) : v=0 := by
  have hb0 : (X^2*Y^2 + X*Y^2*a + Y^2)≠0 := by
    intro hz
    apply hD0
    calc (X^2*Y^2 + X*Y^2*a + Y^2) = (1:ℂ)*(X^2*Y^2 + X*Y^2*a + Y^2) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb1 : ((2)*X^2 + (2)*X*a + (2))≠0 := by
    intro hz
    apply hD1
    calc ((2)*X^2 + (2)*X*a + (2)) = (1:ℂ)*((2)*X^2 + (2)*X*a + (2)) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb2 : (X^4 + X*a + (-1)*Y*b + (-1))≠0 := by
    intro hz
    apply hD2
    calc (X^4 + X*a + (-1)*Y*b + (-1)) = (1:ℂ)*(X^4 + X*a + (-1)*Y*b + (-1)) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb3 : (Y^2 + Y*b + (5))≠0 := by
    intro hz
    apply hD3
    calc (Y^2 + Y*b + (5)) = (1:ℂ)*(Y^2 + Y*b + (5)) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb4 : (X^2 + X*a)≠0 := by
    intro hz
    apply hD4
    calc (X^2 + X*a) = (1:ℂ)*(X^2 + X*a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb5 : (X + a)≠0 := by
    intro hz
    apply hD5
    calc (X + a) = (1:ℂ)*(X + a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb6 : (X^4 + X^3*a)≠0 := by
    intro hz
    apply hD6
    calc (X^4 + X^3*a) = (1:ℂ)*(X^4 + X^3*a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb7 : (X^3 + X^2*a)≠0 := by
    intro hz
    apply hD7
    calc (X^3 + X^2*a) = (1:ℂ)*(X^3 + X^2*a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb8 : (X^6 + X^5*a)≠0 := by
    intro hz
    apply hD8
    calc (X^6 + X^5*a) = (1:ℂ)*(X^6 + X^5*a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb9 : (X^5 + X^4*a)≠0 := by
    intro hz
    apply hD9
    calc (X^5 + X^4*a) = (1:ℂ)*(X^5 + X^4*a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb10 : (X^6 + X^5*a + X^4*a^2 + (2)*X^3*a + X^2*a^2 + X*a + (1))≠0 := by
    intro hz
    apply hD10
    calc (X^6 + X^5*a + X^4*a^2 + (2)*X^3*a + X^2*a^2 + X*a + (1)) = (1:ℂ)*(X^6 + X^5*a + X^4*a^2 + (2)*X^3*a + X^2*a^2 + X*a + (1)) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hh : selectedRowsV3_1 X Y (-Z) (-W) a b v=0 := by
    rw [← rows2_sign_change X Y Z W a b hX hY hZ hW v]
    exact hv
  exact selected_kernel_v3_case1 X Y (-Z) (-W) a b hX hY (neg_ne_zero.mpr hZ) (neg_ne_zero.mpr hW) hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 v hh
#print axioms selected_kernel_gauge_case2


theorem selected_kernel_gauge_case3 (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (hD0 : (X^2*Y^2 + X*Y^2*a + Y^2)≠0)
    (hD1 : ((2)*X^2 + (2)*X*a + (2))≠0)
    (hD2 : (X^4 + X*a + (-1)*Y*b + (-1))≠0)
    (hD3 : (Y^2 + Y*b + (5))≠0)
    (hD4 : (X^2 + X*a)≠0)
    (hD5 : (X + a)≠0)
    (hD6 : (X^4 + X^3*a)≠0)
    (hD7 : (X^3 + X^2*a)≠0)
    (hD8 : (X^6 + X^5*a)≠0)
    (hD9 : (X^5 + X^4*a)≠0)
    (hD10 : (X^6 + X^5*a + X^4*a^2 + (2)*X^3*a + X^2*a^2 + X*a + (1))≠0)
    (v:Fin 210→ℂ) (hv:selectedRowsV3_3 X Y Z W a b v=0) : v=0 := by
  have hb0 : (X^2*Y^2 + X*Y^2*a + Y^2)≠0 := by
    intro hz
    apply hD0
    calc (X^2*Y^2 + X*Y^2*a + Y^2) = (1:ℂ)*(X^2*Y^2 + X*Y^2*a + Y^2) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb1 : ((2)*X^2 + (2)*X*a + (2))≠0 := by
    intro hz
    apply hD1
    calc ((2)*X^2 + (2)*X*a + (2)) = (1:ℂ)*((2)*X^2 + (2)*X*a + (2)) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb2 : (X^4 + X*a + (-1)*Y*b + (-1))≠0 := by
    intro hz
    apply hD2
    calc (X^4 + X*a + (-1)*Y*b + (-1)) = (1:ℂ)*(X^4 + X*a + (-1)*Y*b + (-1)) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb3 : (Y^2 + Y*b + (5))≠0 := by
    intro hz
    apply hD3
    calc (Y^2 + Y*b + (5)) = (1:ℂ)*(Y^2 + Y*b + (5)) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb4 : (X^2 + X*a)≠0 := by
    intro hz
    apply hD4
    calc (X^2 + X*a) = (1:ℂ)*(X^2 + X*a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb5 : (X + a)≠0 := by
    intro hz
    apply hD5
    calc (X + a) = (1:ℂ)*(X + a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb6 : (X^4 + X^3*a)≠0 := by
    intro hz
    apply hD6
    calc (X^4 + X^3*a) = (1:ℂ)*(X^4 + X^3*a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb7 : (X^3 + X^2*a)≠0 := by
    intro hz
    apply hD7
    calc (X^3 + X^2*a) = (1:ℂ)*(X^3 + X^2*a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb8 : (X^6 + X^5*a)≠0 := by
    intro hz
    apply hD8
    calc (X^6 + X^5*a) = (1:ℂ)*(X^6 + X^5*a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb9 : (X^5 + X^4*a)≠0 := by
    intro hz
    apply hD9
    calc (X^5 + X^4*a) = (1:ℂ)*(X^5 + X^4*a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb10 : (X^6 + X^5*a + X^4*a^2 + (2)*X^3*a + X^2*a^2 + X*a + (1))≠0 := by
    intro hz
    apply hD10
    calc (X^6 + X^5*a + X^4*a^2 + (2)*X^3*a + X^2*a^2 + X*a + (1)) = (1:ℂ)*(X^6 + X^5*a + X^4*a^2 + (2)*X^3*a + X^2*a^2 + X*a + (1)) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hh : selectedRowsV3_0 X Y (-Z) (-W) a b v=0 := by
    rw [← rows3_sign_change X Y Z W a b hX hY hZ hW v]
    exact hv
  exact selected_kernel_v3_case0 X Y (-Z) (-W) a b hX hY (neg_ne_zero.mpr hZ) (neg_ne_zero.mpr hW) hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 v hh
#print axioms selected_kernel_gauge_case3


theorem selected_kernel_gauge_case4 (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (hD0 : (X^2*Y^2 + X*Y^2*a + Y^2)≠0)
    (hD1 : ((2)*X^2 + (2)*X*a + (2))≠0)
    (hD2 : (X^4 + X*a + (-1)*Y*b + (-1))≠0)
    (hD3 : (Y^2 + Y*b + (5))≠0)
    (hD4 : (X^2 + X*a)≠0)
    (hD5 : (X + a)≠0)
    (hD6 : (X^4 + X^3*a)≠0)
    (hD7 : (X^3 + X^2*a)≠0)
    (hD8 : (X^6 + X^5*a)≠0)
    (hD9 : (X^5 + X^4*a)≠0)
    (hD10 : (X^6 + X^5*a + X^4*a^2 + (2)*X^3*a + X^2*a^2 + X*a + (1))≠0)
    (v:Fin 210→ℂ) (hv:selectedRowsV3_4 X Y Z W a b v=0) : v=0 := by
  have hb0 : (X^2*Y^2 + X*Y^2*a + Y^2)≠0 := by
    intro hz
    apply hD0
    calc (X^2*Y^2 + X*Y^2*a + Y^2) = (1:ℂ)*(X^2*Y^2 + X*Y^2*a + Y^2) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb1 : ((2)*X^2 + (2)*X*a + (2))≠0 := by
    intro hz
    apply hD1
    calc ((2)*X^2 + (2)*X*a + (2)) = (1:ℂ)*((2)*X^2 + (2)*X*a + (2)) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb2 : (X^4 + X*a + (-1)*Y*b + (-1))≠0 := by
    intro hz
    apply hD2
    calc (X^4 + X*a + (-1)*Y*b + (-1)) = (1:ℂ)*(X^4 + X*a + (-1)*Y*b + (-1)) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb3 : (Y^2 + Y*b + (5))≠0 := by
    intro hz
    apply hD3
    calc (Y^2 + Y*b + (5)) = (1:ℂ)*(Y^2 + Y*b + (5)) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb4 : (X^2 + X*a)≠0 := by
    intro hz
    apply hD4
    calc (X^2 + X*a) = (1:ℂ)*(X^2 + X*a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb5 : (X + a)≠0 := by
    intro hz
    apply hD5
    calc (X + a) = (1:ℂ)*(X + a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb6 : (X^4 + X^3*a)≠0 := by
    intro hz
    apply hD6
    calc (X^4 + X^3*a) = (1:ℂ)*(X^4 + X^3*a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb7 : (X^3 + X^2*a)≠0 := by
    intro hz
    apply hD7
    calc (X^3 + X^2*a) = (1:ℂ)*(X^3 + X^2*a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb8 : (X^6 + X^5*a)≠0 := by
    intro hz
    apply hD8
    calc (X^6 + X^5*a) = (1:ℂ)*(X^6 + X^5*a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb9 : (X^5 + X^4*a)≠0 := by
    intro hz
    apply hD9
    calc (X^5 + X^4*a) = (1:ℂ)*(X^5 + X^4*a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb10 : (X^6 + X^5*a + X^4*a^2 + (2)*X^3*a + X^2*a^2 + X*a + (1))≠0 := by
    intro hz
    apply hD10
    calc (X^6 + X^5*a + X^4*a^2 + (2)*X^3*a + X^2*a^2 + X*a + (1)) = (1:ℂ)*(X^6 + X^5*a + X^4*a^2 + (2)*X^3*a + X^2*a^2 + X*a + (1)) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hh : selectedRowsV3_1 X Y Z (-W) a b v=0 := by
    rw [← rows4_sign_change X Y Z W a b hX hY hZ hW v]
    exact hv
  exact selected_kernel_v3_case1 X Y Z (-W) a b hX hY hZ (neg_ne_zero.mpr hW) hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 v hh
#print axioms selected_kernel_gauge_case4


theorem selected_kernel_gauge_case5 (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (hD0 : (X^2*Y^2 + X*Y^2*a + Y^2)≠0)
    (hD1 : ((2)*X^2 + (2)*X*a + (2))≠0)
    (hD2 : (X^4 + X*a + (-1)*Y*b + (-1))≠0)
    (hD3 : (Y^2 + Y*b + (5))≠0)
    (hD4 : (X^2 + X*a)≠0)
    (hD5 : (X + a)≠0)
    (hD6 : (X^4 + X^3*a)≠0)
    (hD7 : (X^3 + X^2*a)≠0)
    (hD8 : (X^6 + X^5*a)≠0)
    (hD9 : (X^5 + X^4*a)≠0)
    (hD10 : (X^6 + X^5*a + X^4*a^2 + (2)*X^3*a + X^2*a^2 + X*a + (1))≠0)
    (v:Fin 210→ℂ) (hv:selectedRowsV3_5 X Y Z W a b v=0) : v=0 := by
  have hb0 : (X^2*Y^2 + X*Y^2*a + Y^2)≠0 := by
    intro hz
    apply hD0
    calc (X^2*Y^2 + X*Y^2*a + Y^2) = (1:ℂ)*(X^2*Y^2 + X*Y^2*a + Y^2) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb1 : ((2)*X^2 + (2)*X*a + (2))≠0 := by
    intro hz
    apply hD1
    calc ((2)*X^2 + (2)*X*a + (2)) = (1:ℂ)*((2)*X^2 + (2)*X*a + (2)) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb2 : (X^4 + X*a + (-1)*Y*b + (-1))≠0 := by
    intro hz
    apply hD2
    calc (X^4 + X*a + (-1)*Y*b + (-1)) = (1:ℂ)*(X^4 + X*a + (-1)*Y*b + (-1)) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb3 : (Y^2 + Y*b + (5))≠0 := by
    intro hz
    apply hD3
    calc (Y^2 + Y*b + (5)) = (1:ℂ)*(Y^2 + Y*b + (5)) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb4 : (X^2 + X*a)≠0 := by
    intro hz
    apply hD4
    calc (X^2 + X*a) = (1:ℂ)*(X^2 + X*a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb5 : (X + a)≠0 := by
    intro hz
    apply hD5
    calc (X + a) = (1:ℂ)*(X + a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb6 : (X^4 + X^3*a)≠0 := by
    intro hz
    apply hD6
    calc (X^4 + X^3*a) = (1:ℂ)*(X^4 + X^3*a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb7 : (X^3 + X^2*a)≠0 := by
    intro hz
    apply hD7
    calc (X^3 + X^2*a) = (1:ℂ)*(X^3 + X^2*a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb8 : (X^6 + X^5*a)≠0 := by
    intro hz
    apply hD8
    calc (X^6 + X^5*a) = (1:ℂ)*(X^6 + X^5*a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb9 : (X^5 + X^4*a)≠0 := by
    intro hz
    apply hD9
    calc (X^5 + X^4*a) = (1:ℂ)*(X^5 + X^4*a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb10 : (X^6 + X^5*a + X^4*a^2 + (2)*X^3*a + X^2*a^2 + X*a + (1))≠0 := by
    intro hz
    apply hD10
    calc (X^6 + X^5*a + X^4*a^2 + (2)*X^3*a + X^2*a^2 + X*a + (1)) = (1:ℂ)*(X^6 + X^5*a + X^4*a^2 + (2)*X^3*a + X^2*a^2 + X*a + (1)) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hh : selectedRowsV3_0 X Y Z (-W) a b v=0 := by
    rw [← rows5_sign_change X Y Z W a b hX hY hZ hW v]
    exact hv
  exact selected_kernel_v3_case0 X Y Z (-W) a b hX hY hZ (neg_ne_zero.mpr hW) hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 v hh
#print axioms selected_kernel_gauge_case5


theorem selected_kernel_gauge_case6 (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (hD0 : (X^2*Y^2 + X*Y^2*a + Y^2)≠0)
    (hD1 : ((2)*X^2 + (2)*X*a + (2))≠0)
    (hD2 : (X^4 + X*a + (-1)*Y*b + (-1))≠0)
    (hD3 : (Y^2 + Y*b + (5))≠0)
    (hD4 : (X^2 + X*a)≠0)
    (hD5 : (X + a)≠0)
    (hD6 : (X^4 + X^3*a)≠0)
    (hD7 : (X^3 + X^2*a)≠0)
    (hD8 : (X^6 + X^5*a)≠0)
    (hD9 : (X^5 + X^4*a)≠0)
    (hD10 : (X^6 + X^5*a + X^4*a^2 + (2)*X^3*a + X^2*a^2 + X*a + (1))≠0)
    (v:Fin 210→ℂ) (hv:selectedRowsV3_6 X Y Z W a b v=0) : v=0 := by
  have hb0 : (X^2*Y^2 + X*Y^2*a + Y^2)≠0 := by
    intro hz
    apply hD0
    calc (X^2*Y^2 + X*Y^2*a + Y^2) = (1:ℂ)*(X^2*Y^2 + X*Y^2*a + Y^2) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb1 : ((2)*X^2 + (2)*X*a + (2))≠0 := by
    intro hz
    apply hD1
    calc ((2)*X^2 + (2)*X*a + (2)) = (1:ℂ)*((2)*X^2 + (2)*X*a + (2)) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb2 : (X^4 + X*a + (-1)*Y*b + (-1))≠0 := by
    intro hz
    apply hD2
    calc (X^4 + X*a + (-1)*Y*b + (-1)) = (1:ℂ)*(X^4 + X*a + (-1)*Y*b + (-1)) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb3 : (Y^2 + Y*b + (5))≠0 := by
    intro hz
    apply hD3
    calc (Y^2 + Y*b + (5)) = (1:ℂ)*(Y^2 + Y*b + (5)) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb4 : (X^2 + X*a)≠0 := by
    intro hz
    apply hD4
    calc (X^2 + X*a) = (1:ℂ)*(X^2 + X*a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb5 : (X + a)≠0 := by
    intro hz
    apply hD5
    calc (X + a) = (1:ℂ)*(X + a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb6 : (X^4 + X^3*a)≠0 := by
    intro hz
    apply hD6
    calc (X^4 + X^3*a) = (1:ℂ)*(X^4 + X^3*a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb7 : (X^3 + X^2*a)≠0 := by
    intro hz
    apply hD7
    calc (X^3 + X^2*a) = (1:ℂ)*(X^3 + X^2*a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb8 : (X^6 + X^5*a)≠0 := by
    intro hz
    apply hD8
    calc (X^6 + X^5*a) = (1:ℂ)*(X^6 + X^5*a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb9 : (X^5 + X^4*a)≠0 := by
    intro hz
    apply hD9
    calc (X^5 + X^4*a) = (1:ℂ)*(X^5 + X^4*a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb10 : (X^6 + X^5*a + X^4*a^2 + (2)*X^3*a + X^2*a^2 + X*a + (1))≠0 := by
    intro hz
    apply hD10
    calc (X^6 + X^5*a + X^4*a^2 + (2)*X^3*a + X^2*a^2 + X*a + (1)) = (1:ℂ)*(X^6 + X^5*a + X^4*a^2 + (2)*X^3*a + X^2*a^2 + X*a + (1)) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hh : selectedRowsV3_0 X Y (-Z) W a b v=0 := by
    rw [← rows6_sign_change X Y Z W a b hX hY hZ hW v]
    exact hv
  exact selected_kernel_v3_case0 X Y (-Z) W a b hX hY (neg_ne_zero.mpr hZ) hW hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 v hh
#print axioms selected_kernel_gauge_case6


theorem selected_kernel_gauge_case7 (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (hD0 : (X^2*Y^2 + X*Y^2*a + Y^2)≠0)
    (hD1 : ((2)*X^2 + (2)*X*a + (2))≠0)
    (hD2 : (X^4 + X*a + (-1)*Y*b + (-1))≠0)
    (hD3 : (Y^2 + Y*b + (5))≠0)
    (hD4 : (X^2 + X*a)≠0)
    (hD5 : (X + a)≠0)
    (hD6 : (X^4 + X^3*a)≠0)
    (hD7 : (X^3 + X^2*a)≠0)
    (hD8 : (X^6 + X^5*a)≠0)
    (hD9 : (X^5 + X^4*a)≠0)
    (hD10 : (X^6 + X^5*a + X^4*a^2 + (2)*X^3*a + X^2*a^2 + X*a + (1))≠0)
    (v:Fin 210→ℂ) (hv:selectedRowsV3_7 X Y Z W a b v=0) : v=0 := by
  have hb0 : (X^2*Y^2 + X*Y^2*a + Y^2)≠0 := by
    intro hz
    apply hD0
    calc (X^2*Y^2 + X*Y^2*a + Y^2) = (1:ℂ)*(X^2*Y^2 + X*Y^2*a + Y^2) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb1 : ((2)*X^2 + (2)*X*a + (2))≠0 := by
    intro hz
    apply hD1
    calc ((2)*X^2 + (2)*X*a + (2)) = (1:ℂ)*((2)*X^2 + (2)*X*a + (2)) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb2 : (X^4 + X*a + (-1)*Y*b + (-1))≠0 := by
    intro hz
    apply hD2
    calc (X^4 + X*a + (-1)*Y*b + (-1)) = (1:ℂ)*(X^4 + X*a + (-1)*Y*b + (-1)) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb3 : (Y^2 + Y*b + (5))≠0 := by
    intro hz
    apply hD3
    calc (Y^2 + Y*b + (5)) = (1:ℂ)*(Y^2 + Y*b + (5)) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb4 : (X^2 + X*a)≠0 := by
    intro hz
    apply hD4
    calc (X^2 + X*a) = (1:ℂ)*(X^2 + X*a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb5 : (X + a)≠0 := by
    intro hz
    apply hD5
    calc (X + a) = (1:ℂ)*(X + a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb6 : (X^4 + X^3*a)≠0 := by
    intro hz
    apply hD6
    calc (X^4 + X^3*a) = (1:ℂ)*(X^4 + X^3*a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb7 : (X^3 + X^2*a)≠0 := by
    intro hz
    apply hD7
    calc (X^3 + X^2*a) = (1:ℂ)*(X^3 + X^2*a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb8 : (X^6 + X^5*a)≠0 := by
    intro hz
    apply hD8
    calc (X^6 + X^5*a) = (1:ℂ)*(X^6 + X^5*a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb9 : (X^5 + X^4*a)≠0 := by
    intro hz
    apply hD9
    calc (X^5 + X^4*a) = (1:ℂ)*(X^5 + X^4*a) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hb10 : (X^6 + X^5*a + X^4*a^2 + (2)*X^3*a + X^2*a^2 + X*a + (1))≠0 := by
    intro hz
    apply hD10
    calc (X^6 + X^5*a + X^4*a^2 + (2)*X^3*a + X^2*a^2 + X*a + (1)) = (1:ℂ)*(X^6 + X^5*a + X^4*a^2 + (2)*X^3*a + X^2*a^2 + X*a + (1)) := by ring1
         _ = 0 := by rw [hz]; ring1
  have hh : selectedRowsV3_1 X Y (-Z) W a b v=0 := by
    rw [← rows7_sign_change X Y Z W a b hX hY hZ hW v]
    exact hv
  exact selected_kernel_v3_case1 X Y (-Z) W a b hX hY (neg_ne_zero.mpr hZ) hW hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 v hh
#print axioms selected_kernel_gauge_case7

end QuantitativeArithmeticSmallLevelThirtyFiveFullGrid
end
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveFullGridWitnessCaseBundleV4 -/
section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyFiveFullGrid
open Complex

def denom0_0 (X Y Z W a b : ℂ) : ℂ := (X^2*Y^2 + X*Y^2*a + Y^2)
theorem denom0_0_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom0_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom0_0
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0),
    Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ)≠0)]
  fun_prop
theorem denom0_0_witness (a b : ℂ) : ∃ s : ℂ, denom0_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  norm_num [denom0_0,Complex.cpow_natCast] at h0 h1 h2
  have hbad : (1:ℂ)=0 := by
    linear_combination (1/3:ℂ)*h0 + (-1/18:ℂ)*h1 + (1/486:ℂ)*h2
  norm_num at hbad
#print axioms denom0_0_witness
def denom0_1 (X Y Z W a b : ℂ) : ℂ := ((2)*X^2 + (2)*X*a + (2))
theorem denom0_1_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom0_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom0_1
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom0_1_witness (a b : ℂ) : ∃ s : ℂ, denom0_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  norm_num [denom0_1,Complex.cpow_natCast] at h0 h1 h2
  have hbad : (2:ℂ)=0 := by
    linear_combination (1/3:ℂ)*h0 + (-1/2:ℂ)*h1 + (1/6:ℂ)*h2
  norm_num at hbad
#print axioms denom0_1_witness
def denom0_2 (X Y Z W a b : ℂ) : ℂ := (X^4 + X*a + (-1)*Y*b + (-1))
theorem denom0_2_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom0_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom0_2
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0),
    Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ)≠0)]
  fun_prop
theorem denom0_2_witness (a b : ℂ) : ∃ s : ℂ, denom0_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  have h3 := hw (3:ℂ)
  norm_num [denom0_2,Complex.cpow_natCast] at h0 h1 h2 h3
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/455:ℂ)*h0 + (11/2730:ℂ)*h1 + (-1/455:ℂ)*h2 + (1/2730:ℂ)*h3
  norm_num at hbad
#print axioms denom0_2_witness
def denom0_3 (X Y Z W a b : ℂ) : ℂ := (Y^2 + Y*b + (5))
theorem denom0_3_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom0_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom0_3
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ)≠0)]
  fun_prop
theorem denom0_3_witness (a b : ℂ) : ∃ s : ℂ, denom0_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  norm_num [denom0_3,Complex.cpow_natCast] at h0 h1 h2
  have hbad : (1:ℂ)=0 := by
    linear_combination (1/16:ℂ)*h0 + (-1/12:ℂ)*h1 + (1/48:ℂ)*h2
  norm_num at hbad
#print axioms denom0_3_witness
def denom0_4 (X Y Z W a b : ℂ) : ℂ := (X^2 + X*a)
theorem denom0_4_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom0_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom0_4
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom0_4_witness (a b : ℂ) : ∃ s : ℂ, denom0_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom0_4,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/2:ℂ)*h1
  norm_num at hbad
#print axioms denom0_4_witness
def denom0_5 (X Y Z W a b : ℂ) : ℂ := (X + a)
theorem denom0_5_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom0_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom0_5
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom0_5_witness (a b : ℂ) : ∃ s : ℂ, denom0_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom0_5,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/1:ℂ)*h1
  norm_num at hbad
#print axioms denom0_5_witness
def denom0_6 (X Y Z W a b : ℂ) : ℂ := (X^4 + X^3*a)
theorem denom0_6_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom0_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom0_6
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom0_6_witness (a b : ℂ) : ∃ s : ℂ, denom0_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom0_6,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/8:ℂ)*h1
  norm_num at hbad
#print axioms denom0_6_witness
def denom0_7 (X Y Z W a b : ℂ) : ℂ := (X^3 + X^2*a)
theorem denom0_7_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom0_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom0_7
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom0_7_witness (a b : ℂ) : ∃ s : ℂ, denom0_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom0_7,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/4:ℂ)*h1
  norm_num at hbad
#print axioms denom0_7_witness
def denom0_8 (X Y Z W a b : ℂ) : ℂ := (X^6 + X^5*a)
theorem denom0_8_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom0_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom0_8
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom0_8_witness (a b : ℂ) : ∃ s : ℂ, denom0_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom0_8,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/32:ℂ)*h1
  norm_num at hbad
#print axioms denom0_8_witness
def denom0_9 (X Y Z W a b : ℂ) : ℂ := (X^5 + X^4*a)
theorem denom0_9_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom0_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom0_9
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom0_9_witness (a b : ℂ) : ∃ s : ℂ, denom0_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom0_9,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/16:ℂ)*h1
  norm_num at hbad
#print axioms denom0_9_witness
def denom0_10 (X Y Z W a b : ℂ) : ℂ := (X^6 + X^5*a + X^4*a^2 + (2)*X^3*a + X^2*a^2 + X*a + (1))
theorem denom0_10_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom0_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom0_10
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom0_10_witness (a b : ℂ) : ∃ s : ℂ, denom0_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  have h3 := hw (3:ℂ)
  have h4 := hw (4:ℂ)
  have h5 := hw (5:ℂ)
  have h6 := hw (6:ℂ)
  norm_num [denom0_10,Complex.cpow_natCast] at h0 h1 h2 h3 h4 h5 h6
  have hbad : (1:ℂ)=0 := by
    linear_combination (1/615195:ℂ)*h0 + (-1/312480:ℂ)*h1 + (1/483840:ℂ)*h2 + (-1/1806336:ℂ)*h3 + (1/15482880:ℂ)*h4 + (-1/319979520:ℂ)*h5 + (1/20158709760:ℂ)*h6
  norm_num at hbad
#print axioms denom0_10_witness

def denom1_0 (X Y Z W a b : ℂ) : ℂ := (X^2*Y^2 + X*Y^2*a + Y^2)
theorem denom1_0_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom1_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom1_0
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0),
    Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ)≠0)]
  fun_prop
theorem denom1_0_witness (a b : ℂ) : ∃ s : ℂ, denom1_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  norm_num [denom1_0,Complex.cpow_natCast] at h0 h1 h2
  have hbad : (1:ℂ)=0 := by
    linear_combination (1/3:ℂ)*h0 + (-1/18:ℂ)*h1 + (1/486:ℂ)*h2
  norm_num at hbad
#print axioms denom1_0_witness
def denom1_1 (X Y Z W a b : ℂ) : ℂ := ((2)*X^2 + (2)*X*a + (2))
theorem denom1_1_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom1_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom1_1
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom1_1_witness (a b : ℂ) : ∃ s : ℂ, denom1_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  norm_num [denom1_1,Complex.cpow_natCast] at h0 h1 h2
  have hbad : (2:ℂ)=0 := by
    linear_combination (1/3:ℂ)*h0 + (-1/2:ℂ)*h1 + (1/6:ℂ)*h2
  norm_num at hbad
#print axioms denom1_1_witness
def denom1_2 (X Y Z W a b : ℂ) : ℂ := (X^4 + X*a + (-1)*Y*b + (-1))
theorem denom1_2_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom1_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom1_2
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0),
    Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ)≠0)]
  fun_prop
theorem denom1_2_witness (a b : ℂ) : ∃ s : ℂ, denom1_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  have h3 := hw (3:ℂ)
  norm_num [denom1_2,Complex.cpow_natCast] at h0 h1 h2 h3
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/455:ℂ)*h0 + (11/2730:ℂ)*h1 + (-1/455:ℂ)*h2 + (1/2730:ℂ)*h3
  norm_num at hbad
#print axioms denom1_2_witness
def denom1_3 (X Y Z W a b : ℂ) : ℂ := (Y^2 + Y*b + (5))
theorem denom1_3_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom1_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom1_3
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ)≠0)]
  fun_prop
theorem denom1_3_witness (a b : ℂ) : ∃ s : ℂ, denom1_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  norm_num [denom1_3,Complex.cpow_natCast] at h0 h1 h2
  have hbad : (1:ℂ)=0 := by
    linear_combination (1/16:ℂ)*h0 + (-1/12:ℂ)*h1 + (1/48:ℂ)*h2
  norm_num at hbad
#print axioms denom1_3_witness
def denom1_4 (X Y Z W a b : ℂ) : ℂ := (X^2 + X*a)
theorem denom1_4_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom1_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom1_4
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom1_4_witness (a b : ℂ) : ∃ s : ℂ, denom1_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom1_4,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/2:ℂ)*h1
  norm_num at hbad
#print axioms denom1_4_witness
def denom1_5 (X Y Z W a b : ℂ) : ℂ := (X + a)
theorem denom1_5_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom1_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom1_5
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom1_5_witness (a b : ℂ) : ∃ s : ℂ, denom1_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom1_5,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/1:ℂ)*h1
  norm_num at hbad
#print axioms denom1_5_witness
def denom1_6 (X Y Z W a b : ℂ) : ℂ := (X^4 + X^3*a)
theorem denom1_6_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom1_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom1_6
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom1_6_witness (a b : ℂ) : ∃ s : ℂ, denom1_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom1_6,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/8:ℂ)*h1
  norm_num at hbad
#print axioms denom1_6_witness
def denom1_7 (X Y Z W a b : ℂ) : ℂ := (X^3 + X^2*a)
theorem denom1_7_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom1_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom1_7
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom1_7_witness (a b : ℂ) : ∃ s : ℂ, denom1_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom1_7,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/4:ℂ)*h1
  norm_num at hbad
#print axioms denom1_7_witness
def denom1_8 (X Y Z W a b : ℂ) : ℂ := (X^6 + X^5*a)
theorem denom1_8_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom1_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom1_8
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom1_8_witness (a b : ℂ) : ∃ s : ℂ, denom1_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom1_8,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/32:ℂ)*h1
  norm_num at hbad
#print axioms denom1_8_witness
def denom1_9 (X Y Z W a b : ℂ) : ℂ := (X^5 + X^4*a)
theorem denom1_9_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom1_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom1_9
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom1_9_witness (a b : ℂ) : ∃ s : ℂ, denom1_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom1_9,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/16:ℂ)*h1
  norm_num at hbad
#print axioms denom1_9_witness
def denom1_10 (X Y Z W a b : ℂ) : ℂ := (X^6 + X^5*a + X^4*a^2 + (2)*X^3*a + X^2*a^2 + X*a + (1))
theorem denom1_10_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom1_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom1_10
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom1_10_witness (a b : ℂ) : ∃ s : ℂ, denom1_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  have h3 := hw (3:ℂ)
  have h4 := hw (4:ℂ)
  have h5 := hw (5:ℂ)
  have h6 := hw (6:ℂ)
  norm_num [denom1_10,Complex.cpow_natCast] at h0 h1 h2 h3 h4 h5 h6
  have hbad : (1:ℂ)=0 := by
    linear_combination (1/615195:ℂ)*h0 + (-1/312480:ℂ)*h1 + (1/483840:ℂ)*h2 + (-1/1806336:ℂ)*h3 + (1/15482880:ℂ)*h4 + (-1/319979520:ℂ)*h5 + (1/20158709760:ℂ)*h6
  norm_num at hbad
#print axioms denom1_10_witness

def denom2_0 (X Y Z W a b : ℂ) : ℂ := (X^2*Y^2 + X*Y^2*a + Y^2)
theorem denom2_0_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom2_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom2_0
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0),
    Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ)≠0)]
  fun_prop
theorem denom2_0_witness (a b : ℂ) : ∃ s : ℂ, denom2_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  norm_num [denom2_0,Complex.cpow_natCast] at h0 h1 h2
  have hbad : (1:ℂ)=0 := by
    linear_combination (1/3:ℂ)*h0 + (-1/18:ℂ)*h1 + (1/486:ℂ)*h2
  norm_num at hbad
#print axioms denom2_0_witness
def denom2_1 (X Y Z W a b : ℂ) : ℂ := ((2)*X^2 + (2)*X*a + (2))
theorem denom2_1_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom2_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom2_1
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom2_1_witness (a b : ℂ) : ∃ s : ℂ, denom2_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  norm_num [denom2_1,Complex.cpow_natCast] at h0 h1 h2
  have hbad : (2:ℂ)=0 := by
    linear_combination (1/3:ℂ)*h0 + (-1/2:ℂ)*h1 + (1/6:ℂ)*h2
  norm_num at hbad
#print axioms denom2_1_witness
def denom2_2 (X Y Z W a b : ℂ) : ℂ := (X^4 + X*a + (-1)*Y*b + (-1))
theorem denom2_2_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom2_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom2_2
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0),
    Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ)≠0)]
  fun_prop
theorem denom2_2_witness (a b : ℂ) : ∃ s : ℂ, denom2_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  have h3 := hw (3:ℂ)
  norm_num [denom2_2,Complex.cpow_natCast] at h0 h1 h2 h3
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/455:ℂ)*h0 + (11/2730:ℂ)*h1 + (-1/455:ℂ)*h2 + (1/2730:ℂ)*h3
  norm_num at hbad
#print axioms denom2_2_witness
def denom2_3 (X Y Z W a b : ℂ) : ℂ := (Y^2 + Y*b + (5))
theorem denom2_3_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom2_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom2_3
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ)≠0)]
  fun_prop
theorem denom2_3_witness (a b : ℂ) : ∃ s : ℂ, denom2_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  norm_num [denom2_3,Complex.cpow_natCast] at h0 h1 h2
  have hbad : (1:ℂ)=0 := by
    linear_combination (1/16:ℂ)*h0 + (-1/12:ℂ)*h1 + (1/48:ℂ)*h2
  norm_num at hbad
#print axioms denom2_3_witness
def denom2_4 (X Y Z W a b : ℂ) : ℂ := (X^2 + X*a)
theorem denom2_4_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom2_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom2_4
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom2_4_witness (a b : ℂ) : ∃ s : ℂ, denom2_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom2_4,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/2:ℂ)*h1
  norm_num at hbad
#print axioms denom2_4_witness
def denom2_5 (X Y Z W a b : ℂ) : ℂ := (X + a)
theorem denom2_5_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom2_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom2_5
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom2_5_witness (a b : ℂ) : ∃ s : ℂ, denom2_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom2_5,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/1:ℂ)*h1
  norm_num at hbad
#print axioms denom2_5_witness
def denom2_6 (X Y Z W a b : ℂ) : ℂ := (X^4 + X^3*a)
theorem denom2_6_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom2_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom2_6
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom2_6_witness (a b : ℂ) : ∃ s : ℂ, denom2_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom2_6,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/8:ℂ)*h1
  norm_num at hbad
#print axioms denom2_6_witness
def denom2_7 (X Y Z W a b : ℂ) : ℂ := (X^3 + X^2*a)
theorem denom2_7_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom2_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom2_7
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom2_7_witness (a b : ℂ) : ∃ s : ℂ, denom2_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom2_7,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/4:ℂ)*h1
  norm_num at hbad
#print axioms denom2_7_witness
def denom2_8 (X Y Z W a b : ℂ) : ℂ := (X^6 + X^5*a)
theorem denom2_8_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom2_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom2_8
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom2_8_witness (a b : ℂ) : ∃ s : ℂ, denom2_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom2_8,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/32:ℂ)*h1
  norm_num at hbad
#print axioms denom2_8_witness
def denom2_9 (X Y Z W a b : ℂ) : ℂ := (X^5 + X^4*a)
theorem denom2_9_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom2_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom2_9
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom2_9_witness (a b : ℂ) : ∃ s : ℂ, denom2_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom2_9,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/16:ℂ)*h1
  norm_num at hbad
#print axioms denom2_9_witness
def denom2_10 (X Y Z W a b : ℂ) : ℂ := (X^6 + X^5*a + X^4*a^2 + (2)*X^3*a + X^2*a^2 + X*a + (1))
theorem denom2_10_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom2_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom2_10
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom2_10_witness (a b : ℂ) : ∃ s : ℂ, denom2_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  have h3 := hw (3:ℂ)
  have h4 := hw (4:ℂ)
  have h5 := hw (5:ℂ)
  have h6 := hw (6:ℂ)
  norm_num [denom2_10,Complex.cpow_natCast] at h0 h1 h2 h3 h4 h5 h6
  have hbad : (1:ℂ)=0 := by
    linear_combination (1/615195:ℂ)*h0 + (-1/312480:ℂ)*h1 + (1/483840:ℂ)*h2 + (-1/1806336:ℂ)*h3 + (1/15482880:ℂ)*h4 + (-1/319979520:ℂ)*h5 + (1/20158709760:ℂ)*h6
  norm_num at hbad
#print axioms denom2_10_witness

def denom3_0 (X Y Z W a b : ℂ) : ℂ := (X^2*Y^2 + X*Y^2*a + Y^2)
theorem denom3_0_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom3_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom3_0
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0),
    Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ)≠0)]
  fun_prop
theorem denom3_0_witness (a b : ℂ) : ∃ s : ℂ, denom3_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  norm_num [denom3_0,Complex.cpow_natCast] at h0 h1 h2
  have hbad : (1:ℂ)=0 := by
    linear_combination (1/3:ℂ)*h0 + (-1/18:ℂ)*h1 + (1/486:ℂ)*h2
  norm_num at hbad
#print axioms denom3_0_witness
def denom3_1 (X Y Z W a b : ℂ) : ℂ := ((2)*X^2 + (2)*X*a + (2))
theorem denom3_1_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom3_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom3_1
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom3_1_witness (a b : ℂ) : ∃ s : ℂ, denom3_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  norm_num [denom3_1,Complex.cpow_natCast] at h0 h1 h2
  have hbad : (2:ℂ)=0 := by
    linear_combination (1/3:ℂ)*h0 + (-1/2:ℂ)*h1 + (1/6:ℂ)*h2
  norm_num at hbad
#print axioms denom3_1_witness
def denom3_2 (X Y Z W a b : ℂ) : ℂ := (X^4 + X*a + (-1)*Y*b + (-1))
theorem denom3_2_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom3_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom3_2
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0),
    Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ)≠0)]
  fun_prop
theorem denom3_2_witness (a b : ℂ) : ∃ s : ℂ, denom3_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  have h3 := hw (3:ℂ)
  norm_num [denom3_2,Complex.cpow_natCast] at h0 h1 h2 h3
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/455:ℂ)*h0 + (11/2730:ℂ)*h1 + (-1/455:ℂ)*h2 + (1/2730:ℂ)*h3
  norm_num at hbad
#print axioms denom3_2_witness
def denom3_3 (X Y Z W a b : ℂ) : ℂ := (Y^2 + Y*b + (5))
theorem denom3_3_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom3_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom3_3
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ)≠0)]
  fun_prop
theorem denom3_3_witness (a b : ℂ) : ∃ s : ℂ, denom3_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  norm_num [denom3_3,Complex.cpow_natCast] at h0 h1 h2
  have hbad : (1:ℂ)=0 := by
    linear_combination (1/16:ℂ)*h0 + (-1/12:ℂ)*h1 + (1/48:ℂ)*h2
  norm_num at hbad
#print axioms denom3_3_witness
def denom3_4 (X Y Z W a b : ℂ) : ℂ := (X^2 + X*a)
theorem denom3_4_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom3_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom3_4
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom3_4_witness (a b : ℂ) : ∃ s : ℂ, denom3_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom3_4,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/2:ℂ)*h1
  norm_num at hbad
#print axioms denom3_4_witness
def denom3_5 (X Y Z W a b : ℂ) : ℂ := (X + a)
theorem denom3_5_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom3_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom3_5
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom3_5_witness (a b : ℂ) : ∃ s : ℂ, denom3_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom3_5,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/1:ℂ)*h1
  norm_num at hbad
#print axioms denom3_5_witness
def denom3_6 (X Y Z W a b : ℂ) : ℂ := (X^4 + X^3*a)
theorem denom3_6_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom3_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom3_6
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom3_6_witness (a b : ℂ) : ∃ s : ℂ, denom3_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom3_6,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/8:ℂ)*h1
  norm_num at hbad
#print axioms denom3_6_witness
def denom3_7 (X Y Z W a b : ℂ) : ℂ := (X^3 + X^2*a)
theorem denom3_7_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom3_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom3_7
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom3_7_witness (a b : ℂ) : ∃ s : ℂ, denom3_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom3_7,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/4:ℂ)*h1
  norm_num at hbad
#print axioms denom3_7_witness
def denom3_8 (X Y Z W a b : ℂ) : ℂ := (X^6 + X^5*a)
theorem denom3_8_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom3_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom3_8
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom3_8_witness (a b : ℂ) : ∃ s : ℂ, denom3_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom3_8,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/32:ℂ)*h1
  norm_num at hbad
#print axioms denom3_8_witness
def denom3_9 (X Y Z W a b : ℂ) : ℂ := (X^5 + X^4*a)
theorem denom3_9_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom3_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom3_9
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom3_9_witness (a b : ℂ) : ∃ s : ℂ, denom3_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom3_9,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/16:ℂ)*h1
  norm_num at hbad
#print axioms denom3_9_witness
def denom3_10 (X Y Z W a b : ℂ) : ℂ := (X^6 + X^5*a + X^4*a^2 + (2)*X^3*a + X^2*a^2 + X*a + (1))
theorem denom3_10_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom3_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom3_10
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom3_10_witness (a b : ℂ) : ∃ s : ℂ, denom3_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  have h3 := hw (3:ℂ)
  have h4 := hw (4:ℂ)
  have h5 := hw (5:ℂ)
  have h6 := hw (6:ℂ)
  norm_num [denom3_10,Complex.cpow_natCast] at h0 h1 h2 h3 h4 h5 h6
  have hbad : (1:ℂ)=0 := by
    linear_combination (1/615195:ℂ)*h0 + (-1/312480:ℂ)*h1 + (1/483840:ℂ)*h2 + (-1/1806336:ℂ)*h3 + (1/15482880:ℂ)*h4 + (-1/319979520:ℂ)*h5 + (1/20158709760:ℂ)*h6
  norm_num at hbad
#print axioms denom3_10_witness

def denom4_0 (X Y Z W a b : ℂ) : ℂ := (X^2*Y^2 + X*Y^2*a + Y^2)
theorem denom4_0_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom4_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom4_0
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0),
    Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ)≠0)]
  fun_prop
theorem denom4_0_witness (a b : ℂ) : ∃ s : ℂ, denom4_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  norm_num [denom4_0,Complex.cpow_natCast] at h0 h1 h2
  have hbad : (1:ℂ)=0 := by
    linear_combination (1/3:ℂ)*h0 + (-1/18:ℂ)*h1 + (1/486:ℂ)*h2
  norm_num at hbad
#print axioms denom4_0_witness
def denom4_1 (X Y Z W a b : ℂ) : ℂ := ((2)*X^2 + (2)*X*a + (2))
theorem denom4_1_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom4_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom4_1
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom4_1_witness (a b : ℂ) : ∃ s : ℂ, denom4_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  norm_num [denom4_1,Complex.cpow_natCast] at h0 h1 h2
  have hbad : (2:ℂ)=0 := by
    linear_combination (1/3:ℂ)*h0 + (-1/2:ℂ)*h1 + (1/6:ℂ)*h2
  norm_num at hbad
#print axioms denom4_1_witness
def denom4_2 (X Y Z W a b : ℂ) : ℂ := (X^4 + X*a + (-1)*Y*b + (-1))
theorem denom4_2_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom4_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom4_2
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0),
    Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ)≠0)]
  fun_prop
theorem denom4_2_witness (a b : ℂ) : ∃ s : ℂ, denom4_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  have h3 := hw (3:ℂ)
  norm_num [denom4_2,Complex.cpow_natCast] at h0 h1 h2 h3
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/455:ℂ)*h0 + (11/2730:ℂ)*h1 + (-1/455:ℂ)*h2 + (1/2730:ℂ)*h3
  norm_num at hbad
#print axioms denom4_2_witness
def denom4_3 (X Y Z W a b : ℂ) : ℂ := (Y^2 + Y*b + (5))
theorem denom4_3_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom4_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom4_3
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ)≠0)]
  fun_prop
theorem denom4_3_witness (a b : ℂ) : ∃ s : ℂ, denom4_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  norm_num [denom4_3,Complex.cpow_natCast] at h0 h1 h2
  have hbad : (1:ℂ)=0 := by
    linear_combination (1/16:ℂ)*h0 + (-1/12:ℂ)*h1 + (1/48:ℂ)*h2
  norm_num at hbad
#print axioms denom4_3_witness
def denom4_4 (X Y Z W a b : ℂ) : ℂ := (X^2 + X*a)
theorem denom4_4_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom4_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom4_4
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom4_4_witness (a b : ℂ) : ∃ s : ℂ, denom4_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom4_4,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/2:ℂ)*h1
  norm_num at hbad
#print axioms denom4_4_witness
def denom4_5 (X Y Z W a b : ℂ) : ℂ := (X + a)
theorem denom4_5_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom4_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom4_5
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom4_5_witness (a b : ℂ) : ∃ s : ℂ, denom4_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom4_5,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/1:ℂ)*h1
  norm_num at hbad
#print axioms denom4_5_witness
def denom4_6 (X Y Z W a b : ℂ) : ℂ := (X^4 + X^3*a)
theorem denom4_6_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom4_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom4_6
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom4_6_witness (a b : ℂ) : ∃ s : ℂ, denom4_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom4_6,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/8:ℂ)*h1
  norm_num at hbad
#print axioms denom4_6_witness
def denom4_7 (X Y Z W a b : ℂ) : ℂ := (X^3 + X^2*a)
theorem denom4_7_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom4_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom4_7
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom4_7_witness (a b : ℂ) : ∃ s : ℂ, denom4_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom4_7,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/4:ℂ)*h1
  norm_num at hbad
#print axioms denom4_7_witness
def denom4_8 (X Y Z W a b : ℂ) : ℂ := (X^6 + X^5*a)
theorem denom4_8_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom4_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom4_8
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom4_8_witness (a b : ℂ) : ∃ s : ℂ, denom4_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom4_8,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/32:ℂ)*h1
  norm_num at hbad
#print axioms denom4_8_witness
def denom4_9 (X Y Z W a b : ℂ) : ℂ := (X^5 + X^4*a)
theorem denom4_9_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom4_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom4_9
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom4_9_witness (a b : ℂ) : ∃ s : ℂ, denom4_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom4_9,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/16:ℂ)*h1
  norm_num at hbad
#print axioms denom4_9_witness
def denom4_10 (X Y Z W a b : ℂ) : ℂ := (X^6 + X^5*a + X^4*a^2 + (2)*X^3*a + X^2*a^2 + X*a + (1))
theorem denom4_10_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom4_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom4_10
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom4_10_witness (a b : ℂ) : ∃ s : ℂ, denom4_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  have h3 := hw (3:ℂ)
  have h4 := hw (4:ℂ)
  have h5 := hw (5:ℂ)
  have h6 := hw (6:ℂ)
  norm_num [denom4_10,Complex.cpow_natCast] at h0 h1 h2 h3 h4 h5 h6
  have hbad : (1:ℂ)=0 := by
    linear_combination (1/615195:ℂ)*h0 + (-1/312480:ℂ)*h1 + (1/483840:ℂ)*h2 + (-1/1806336:ℂ)*h3 + (1/15482880:ℂ)*h4 + (-1/319979520:ℂ)*h5 + (1/20158709760:ℂ)*h6
  norm_num at hbad
#print axioms denom4_10_witness

def denom5_0 (X Y Z W a b : ℂ) : ℂ := (X^2*Y^2 + X*Y^2*a + Y^2)
theorem denom5_0_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom5_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom5_0
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0),
    Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ)≠0)]
  fun_prop
theorem denom5_0_witness (a b : ℂ) : ∃ s : ℂ, denom5_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  norm_num [denom5_0,Complex.cpow_natCast] at h0 h1 h2
  have hbad : (1:ℂ)=0 := by
    linear_combination (1/3:ℂ)*h0 + (-1/18:ℂ)*h1 + (1/486:ℂ)*h2
  norm_num at hbad
#print axioms denom5_0_witness
def denom5_1 (X Y Z W a b : ℂ) : ℂ := ((2)*X^2 + (2)*X*a + (2))
theorem denom5_1_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom5_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom5_1
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom5_1_witness (a b : ℂ) : ∃ s : ℂ, denom5_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  norm_num [denom5_1,Complex.cpow_natCast] at h0 h1 h2
  have hbad : (2:ℂ)=0 := by
    linear_combination (1/3:ℂ)*h0 + (-1/2:ℂ)*h1 + (1/6:ℂ)*h2
  norm_num at hbad
#print axioms denom5_1_witness
def denom5_2 (X Y Z W a b : ℂ) : ℂ := (X^4 + X*a + (-1)*Y*b + (-1))
theorem denom5_2_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom5_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom5_2
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0),
    Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ)≠0)]
  fun_prop
theorem denom5_2_witness (a b : ℂ) : ∃ s : ℂ, denom5_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  have h3 := hw (3:ℂ)
  norm_num [denom5_2,Complex.cpow_natCast] at h0 h1 h2 h3
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/455:ℂ)*h0 + (11/2730:ℂ)*h1 + (-1/455:ℂ)*h2 + (1/2730:ℂ)*h3
  norm_num at hbad
#print axioms denom5_2_witness
def denom5_3 (X Y Z W a b : ℂ) : ℂ := (Y^2 + Y*b + (5))
theorem denom5_3_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom5_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom5_3
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ)≠0)]
  fun_prop
theorem denom5_3_witness (a b : ℂ) : ∃ s : ℂ, denom5_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  norm_num [denom5_3,Complex.cpow_natCast] at h0 h1 h2
  have hbad : (1:ℂ)=0 := by
    linear_combination (1/16:ℂ)*h0 + (-1/12:ℂ)*h1 + (1/48:ℂ)*h2
  norm_num at hbad
#print axioms denom5_3_witness
def denom5_4 (X Y Z W a b : ℂ) : ℂ := (X^2 + X*a)
theorem denom5_4_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom5_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom5_4
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom5_4_witness (a b : ℂ) : ∃ s : ℂ, denom5_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom5_4,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/2:ℂ)*h1
  norm_num at hbad
#print axioms denom5_4_witness
def denom5_5 (X Y Z W a b : ℂ) : ℂ := (X + a)
theorem denom5_5_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom5_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom5_5
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom5_5_witness (a b : ℂ) : ∃ s : ℂ, denom5_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom5_5,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/1:ℂ)*h1
  norm_num at hbad
#print axioms denom5_5_witness
def denom5_6 (X Y Z W a b : ℂ) : ℂ := (X^4 + X^3*a)
theorem denom5_6_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom5_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom5_6
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom5_6_witness (a b : ℂ) : ∃ s : ℂ, denom5_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom5_6,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/8:ℂ)*h1
  norm_num at hbad
#print axioms denom5_6_witness
def denom5_7 (X Y Z W a b : ℂ) : ℂ := (X^3 + X^2*a)
theorem denom5_7_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom5_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom5_7
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom5_7_witness (a b : ℂ) : ∃ s : ℂ, denom5_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom5_7,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/4:ℂ)*h1
  norm_num at hbad
#print axioms denom5_7_witness
def denom5_8 (X Y Z W a b : ℂ) : ℂ := (X^6 + X^5*a)
theorem denom5_8_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom5_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom5_8
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom5_8_witness (a b : ℂ) : ∃ s : ℂ, denom5_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom5_8,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/32:ℂ)*h1
  norm_num at hbad
#print axioms denom5_8_witness
def denom5_9 (X Y Z W a b : ℂ) : ℂ := (X^5 + X^4*a)
theorem denom5_9_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom5_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom5_9
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom5_9_witness (a b : ℂ) : ∃ s : ℂ, denom5_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom5_9,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/16:ℂ)*h1
  norm_num at hbad
#print axioms denom5_9_witness
def denom5_10 (X Y Z W a b : ℂ) : ℂ := (X^6 + X^5*a + X^4*a^2 + (2)*X^3*a + X^2*a^2 + X*a + (1))
theorem denom5_10_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom5_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom5_10
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom5_10_witness (a b : ℂ) : ∃ s : ℂ, denom5_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  have h3 := hw (3:ℂ)
  have h4 := hw (4:ℂ)
  have h5 := hw (5:ℂ)
  have h6 := hw (6:ℂ)
  norm_num [denom5_10,Complex.cpow_natCast] at h0 h1 h2 h3 h4 h5 h6
  have hbad : (1:ℂ)=0 := by
    linear_combination (1/615195:ℂ)*h0 + (-1/312480:ℂ)*h1 + (1/483840:ℂ)*h2 + (-1/1806336:ℂ)*h3 + (1/15482880:ℂ)*h4 + (-1/319979520:ℂ)*h5 + (1/20158709760:ℂ)*h6
  norm_num at hbad
#print axioms denom5_10_witness

def denom6_0 (X Y Z W a b : ℂ) : ℂ := (X^2*Y^2 + X*Y^2*a + Y^2)
theorem denom6_0_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom6_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom6_0
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0),
    Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ)≠0)]
  fun_prop
theorem denom6_0_witness (a b : ℂ) : ∃ s : ℂ, denom6_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  norm_num [denom6_0,Complex.cpow_natCast] at h0 h1 h2
  have hbad : (1:ℂ)=0 := by
    linear_combination (1/3:ℂ)*h0 + (-1/18:ℂ)*h1 + (1/486:ℂ)*h2
  norm_num at hbad
#print axioms denom6_0_witness
def denom6_1 (X Y Z W a b : ℂ) : ℂ := ((2)*X^2 + (2)*X*a + (2))
theorem denom6_1_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom6_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom6_1
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom6_1_witness (a b : ℂ) : ∃ s : ℂ, denom6_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  norm_num [denom6_1,Complex.cpow_natCast] at h0 h1 h2
  have hbad : (2:ℂ)=0 := by
    linear_combination (1/3:ℂ)*h0 + (-1/2:ℂ)*h1 + (1/6:ℂ)*h2
  norm_num at hbad
#print axioms denom6_1_witness
def denom6_2 (X Y Z W a b : ℂ) : ℂ := (X^4 + X*a + (-1)*Y*b + (-1))
theorem denom6_2_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom6_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom6_2
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0),
    Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ)≠0)]
  fun_prop
theorem denom6_2_witness (a b : ℂ) : ∃ s : ℂ, denom6_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  have h3 := hw (3:ℂ)
  norm_num [denom6_2,Complex.cpow_natCast] at h0 h1 h2 h3
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/455:ℂ)*h0 + (11/2730:ℂ)*h1 + (-1/455:ℂ)*h2 + (1/2730:ℂ)*h3
  norm_num at hbad
#print axioms denom6_2_witness
def denom6_3 (X Y Z W a b : ℂ) : ℂ := (Y^2 + Y*b + (5))
theorem denom6_3_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom6_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom6_3
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ)≠0)]
  fun_prop
theorem denom6_3_witness (a b : ℂ) : ∃ s : ℂ, denom6_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  norm_num [denom6_3,Complex.cpow_natCast] at h0 h1 h2
  have hbad : (1:ℂ)=0 := by
    linear_combination (1/16:ℂ)*h0 + (-1/12:ℂ)*h1 + (1/48:ℂ)*h2
  norm_num at hbad
#print axioms denom6_3_witness
def denom6_4 (X Y Z W a b : ℂ) : ℂ := (X^2 + X*a)
theorem denom6_4_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom6_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom6_4
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom6_4_witness (a b : ℂ) : ∃ s : ℂ, denom6_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom6_4,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/2:ℂ)*h1
  norm_num at hbad
#print axioms denom6_4_witness
def denom6_5 (X Y Z W a b : ℂ) : ℂ := (X + a)
theorem denom6_5_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom6_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom6_5
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom6_5_witness (a b : ℂ) : ∃ s : ℂ, denom6_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom6_5,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/1:ℂ)*h1
  norm_num at hbad
#print axioms denom6_5_witness
def denom6_6 (X Y Z W a b : ℂ) : ℂ := (X^4 + X^3*a)
theorem denom6_6_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom6_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom6_6
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom6_6_witness (a b : ℂ) : ∃ s : ℂ, denom6_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom6_6,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/8:ℂ)*h1
  norm_num at hbad
#print axioms denom6_6_witness
def denom6_7 (X Y Z W a b : ℂ) : ℂ := (X^3 + X^2*a)
theorem denom6_7_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom6_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom6_7
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom6_7_witness (a b : ℂ) : ∃ s : ℂ, denom6_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom6_7,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/4:ℂ)*h1
  norm_num at hbad
#print axioms denom6_7_witness
def denom6_8 (X Y Z W a b : ℂ) : ℂ := (X^6 + X^5*a)
theorem denom6_8_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom6_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom6_8
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom6_8_witness (a b : ℂ) : ∃ s : ℂ, denom6_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom6_8,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/32:ℂ)*h1
  norm_num at hbad
#print axioms denom6_8_witness
def denom6_9 (X Y Z W a b : ℂ) : ℂ := (X^5 + X^4*a)
theorem denom6_9_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom6_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom6_9
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom6_9_witness (a b : ℂ) : ∃ s : ℂ, denom6_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom6_9,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/16:ℂ)*h1
  norm_num at hbad
#print axioms denom6_9_witness
def denom6_10 (X Y Z W a b : ℂ) : ℂ := (X^6 + X^5*a + X^4*a^2 + (2)*X^3*a + X^2*a^2 + X*a + (1))
theorem denom6_10_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom6_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom6_10
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom6_10_witness (a b : ℂ) : ∃ s : ℂ, denom6_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  have h3 := hw (3:ℂ)
  have h4 := hw (4:ℂ)
  have h5 := hw (5:ℂ)
  have h6 := hw (6:ℂ)
  norm_num [denom6_10,Complex.cpow_natCast] at h0 h1 h2 h3 h4 h5 h6
  have hbad : (1:ℂ)=0 := by
    linear_combination (1/615195:ℂ)*h0 + (-1/312480:ℂ)*h1 + (1/483840:ℂ)*h2 + (-1/1806336:ℂ)*h3 + (1/15482880:ℂ)*h4 + (-1/319979520:ℂ)*h5 + (1/20158709760:ℂ)*h6
  norm_num at hbad
#print axioms denom6_10_witness

def denom7_0 (X Y Z W a b : ℂ) : ℂ := (X^2*Y^2 + X*Y^2*a + Y^2)
theorem denom7_0_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom7_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom7_0
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0),
    Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ)≠0)]
  fun_prop
theorem denom7_0_witness (a b : ℂ) : ∃ s : ℂ, denom7_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  norm_num [denom7_0,Complex.cpow_natCast] at h0 h1 h2
  have hbad : (1:ℂ)=0 := by
    linear_combination (1/3:ℂ)*h0 + (-1/18:ℂ)*h1 + (1/486:ℂ)*h2
  norm_num at hbad
#print axioms denom7_0_witness
def denom7_1 (X Y Z W a b : ℂ) : ℂ := ((2)*X^2 + (2)*X*a + (2))
theorem denom7_1_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom7_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom7_1
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom7_1_witness (a b : ℂ) : ∃ s : ℂ, denom7_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  norm_num [denom7_1,Complex.cpow_natCast] at h0 h1 h2
  have hbad : (2:ℂ)=0 := by
    linear_combination (1/3:ℂ)*h0 + (-1/2:ℂ)*h1 + (1/6:ℂ)*h2
  norm_num at hbad
#print axioms denom7_1_witness
def denom7_2 (X Y Z W a b : ℂ) : ℂ := (X^4 + X*a + (-1)*Y*b + (-1))
theorem denom7_2_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom7_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom7_2
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0),
    Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ)≠0)]
  fun_prop
theorem denom7_2_witness (a b : ℂ) : ∃ s : ℂ, denom7_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  have h3 := hw (3:ℂ)
  norm_num [denom7_2,Complex.cpow_natCast] at h0 h1 h2 h3
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/455:ℂ)*h0 + (11/2730:ℂ)*h1 + (-1/455:ℂ)*h2 + (1/2730:ℂ)*h3
  norm_num at hbad
#print axioms denom7_2_witness
def denom7_3 (X Y Z W a b : ℂ) : ℂ := (Y^2 + Y*b + (5))
theorem denom7_3_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom7_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom7_3
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ)≠0)]
  fun_prop
theorem denom7_3_witness (a b : ℂ) : ∃ s : ℂ, denom7_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  norm_num [denom7_3,Complex.cpow_natCast] at h0 h1 h2
  have hbad : (1:ℂ)=0 := by
    linear_combination (1/16:ℂ)*h0 + (-1/12:ℂ)*h1 + (1/48:ℂ)*h2
  norm_num at hbad
#print axioms denom7_3_witness
def denom7_4 (X Y Z W a b : ℂ) : ℂ := (X^2 + X*a)
theorem denom7_4_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom7_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom7_4
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom7_4_witness (a b : ℂ) : ∃ s : ℂ, denom7_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom7_4,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/2:ℂ)*h1
  norm_num at hbad
#print axioms denom7_4_witness
def denom7_5 (X Y Z W a b : ℂ) : ℂ := (X + a)
theorem denom7_5_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom7_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom7_5
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom7_5_witness (a b : ℂ) : ∃ s : ℂ, denom7_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom7_5,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/1:ℂ)*h1
  norm_num at hbad
#print axioms denom7_5_witness
def denom7_6 (X Y Z W a b : ℂ) : ℂ := (X^4 + X^3*a)
theorem denom7_6_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom7_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom7_6
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom7_6_witness (a b : ℂ) : ∃ s : ℂ, denom7_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom7_6,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/8:ℂ)*h1
  norm_num at hbad
#print axioms denom7_6_witness
def denom7_7 (X Y Z W a b : ℂ) : ℂ := (X^3 + X^2*a)
theorem denom7_7_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom7_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom7_7
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom7_7_witness (a b : ℂ) : ∃ s : ℂ, denom7_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom7_7,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/4:ℂ)*h1
  norm_num at hbad
#print axioms denom7_7_witness
def denom7_8 (X Y Z W a b : ℂ) : ℂ := (X^6 + X^5*a)
theorem denom7_8_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom7_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom7_8
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom7_8_witness (a b : ℂ) : ∃ s : ℂ, denom7_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom7_8,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/32:ℂ)*h1
  norm_num at hbad
#print axioms denom7_8_witness
def denom7_9 (X Y Z W a b : ℂ) : ℂ := (X^5 + X^4*a)
theorem denom7_9_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom7_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom7_9
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom7_9_witness (a b : ℂ) : ∃ s : ℂ, denom7_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  norm_num [denom7_9,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination (-1/1:ℂ)*h0 + (1/16:ℂ)*h1
  norm_num at hbad
#print axioms denom7_9_witness
def denom7_10 (X Y Z W a b : ℂ) : ℂ := (X^6 + X^5*a + X^4*a^2 + (2)*X^3*a + X^2*a^2 + X*a + (1))
theorem denom7_10_entire (a b : ℂ) : Differentiable ℂ (fun s : ℂ => denom7_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b) := by
  unfold denom7_10
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop
theorem denom7_10_witness (a b : ℂ) : ∃ s : ℂ, denom7_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (0:ℂ)
  have h1 := hw (1:ℂ)
  have h2 := hw (2:ℂ)
  have h3 := hw (3:ℂ)
  have h4 := hw (4:ℂ)
  have h5 := hw (5:ℂ)
  have h6 := hw (6:ℂ)
  norm_num [denom7_10,Complex.cpow_natCast] at h0 h1 h2 h3 h4 h5 h6
  have hbad : (1:ℂ)=0 := by
    linear_combination (1/615195:ℂ)*h0 + (-1/312480:ℂ)*h1 + (1/483840:ℂ)*h2 + (-1/1806336:ℂ)*h3 + (1/15482880:ℂ)*h4 + (-1/319979520:ℂ)*h5 + (1/20158709760:ℂ)*h6
  norm_num at hbad
#print axioms denom7_10_witness

end QuantitativeArithmeticSmallLevelThirtyFiveFullGrid
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveFullGridCommonCaseBundleV4 -/
section
set_option autoImplicit false
set_option maxHeartbeats 0
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyFiveFullGrid
open Complex Filter
open scoped Topology

theorem denominators0_common (a b : ℂ) : ∃ s : ℂ,
    denom0_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom0_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom0_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom0_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom0_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom0_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom0_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom0_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom0_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom0_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom0_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  have h0 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom0_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom0_0_entire a b).analyticAt s) (denom0_0_witness a b) 0
  have h1 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom0_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom0_1_entire a b).analyticAt s) (denom0_1_witness a b) 0
  have h2 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom0_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom0_2_entire a b).analyticAt s) (denom0_2_witness a b) 0
  have h3 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom0_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom0_3_entire a b).analyticAt s) (denom0_3_witness a b) 0
  have h4 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom0_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom0_4_entire a b).analyticAt s) (denom0_4_witness a b) 0
  have h5 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom0_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom0_5_entire a b).analyticAt s) (denom0_5_witness a b) 0
  have h6 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom0_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom0_6_entire a b).analyticAt s) (denom0_6_witness a b) 0
  have h7 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom0_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom0_7_entire a b).analyticAt s) (denom0_7_witness a b) 0
  have h8 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom0_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom0_8_entire a b).analyticAt s) (denom0_8_witness a b) 0
  have h9 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom0_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom0_9_entire a b).analyticAt s) (denom0_9_witness a b) 0
  have h10 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom0_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom0_10_entire a b).analyticAt s) (denom0_10_witness a b) 0
  have hh : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom0_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom0_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom0_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom0_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom0_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom0_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom0_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom0_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom0_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom0_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom0_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
    filter_upwards [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10] with s hh0 hh1 hh2 hh3 hh4 hh5 hh6 hh7 hh8 hh9 hh10
    exact ⟨hh0,hh1,hh2,hh3,hh4,hh5,hh6,hh7,hh8,hh9,hh10⟩
  exact hh.exists
#print axioms denominators0_common

theorem denominators1_common (a b : ℂ) : ∃ s : ℂ,
    denom1_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom1_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom1_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom1_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom1_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom1_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom1_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom1_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom1_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom1_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom1_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  have h0 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom1_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom1_0_entire a b).analyticAt s) (denom1_0_witness a b) 0
  have h1 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom1_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom1_1_entire a b).analyticAt s) (denom1_1_witness a b) 0
  have h2 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom1_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom1_2_entire a b).analyticAt s) (denom1_2_witness a b) 0
  have h3 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom1_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom1_3_entire a b).analyticAt s) (denom1_3_witness a b) 0
  have h4 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom1_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom1_4_entire a b).analyticAt s) (denom1_4_witness a b) 0
  have h5 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom1_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom1_5_entire a b).analyticAt s) (denom1_5_witness a b) 0
  have h6 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom1_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom1_6_entire a b).analyticAt s) (denom1_6_witness a b) 0
  have h7 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom1_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom1_7_entire a b).analyticAt s) (denom1_7_witness a b) 0
  have h8 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom1_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom1_8_entire a b).analyticAt s) (denom1_8_witness a b) 0
  have h9 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom1_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom1_9_entire a b).analyticAt s) (denom1_9_witness a b) 0
  have h10 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom1_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom1_10_entire a b).analyticAt s) (denom1_10_witness a b) 0
  have hh : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom1_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom1_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom1_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom1_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom1_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom1_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom1_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom1_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom1_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom1_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom1_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
    filter_upwards [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10] with s hh0 hh1 hh2 hh3 hh4 hh5 hh6 hh7 hh8 hh9 hh10
    exact ⟨hh0,hh1,hh2,hh3,hh4,hh5,hh6,hh7,hh8,hh9,hh10⟩
  exact hh.exists
#print axioms denominators1_common

theorem denominators2_common (a b : ℂ) : ∃ s : ℂ,
    denom2_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom2_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom2_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom2_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom2_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom2_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom2_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom2_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom2_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom2_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom2_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  have h0 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom2_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom2_0_entire a b).analyticAt s) (denom2_0_witness a b) 0
  have h1 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom2_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom2_1_entire a b).analyticAt s) (denom2_1_witness a b) 0
  have h2 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom2_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom2_2_entire a b).analyticAt s) (denom2_2_witness a b) 0
  have h3 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom2_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom2_3_entire a b).analyticAt s) (denom2_3_witness a b) 0
  have h4 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom2_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom2_4_entire a b).analyticAt s) (denom2_4_witness a b) 0
  have h5 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom2_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom2_5_entire a b).analyticAt s) (denom2_5_witness a b) 0
  have h6 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom2_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom2_6_entire a b).analyticAt s) (denom2_6_witness a b) 0
  have h7 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom2_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom2_7_entire a b).analyticAt s) (denom2_7_witness a b) 0
  have h8 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom2_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom2_8_entire a b).analyticAt s) (denom2_8_witness a b) 0
  have h9 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom2_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom2_9_entire a b).analyticAt s) (denom2_9_witness a b) 0
  have h10 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom2_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom2_10_entire a b).analyticAt s) (denom2_10_witness a b) 0
  have hh : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom2_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom2_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom2_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom2_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom2_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom2_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom2_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom2_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom2_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom2_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom2_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
    filter_upwards [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10] with s hh0 hh1 hh2 hh3 hh4 hh5 hh6 hh7 hh8 hh9 hh10
    exact ⟨hh0,hh1,hh2,hh3,hh4,hh5,hh6,hh7,hh8,hh9,hh10⟩
  exact hh.exists
#print axioms denominators2_common

theorem denominators3_common (a b : ℂ) : ∃ s : ℂ,
    denom3_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom3_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom3_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom3_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom3_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom3_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom3_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom3_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom3_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom3_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom3_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  have h0 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom3_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom3_0_entire a b).analyticAt s) (denom3_0_witness a b) 0
  have h1 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom3_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom3_1_entire a b).analyticAt s) (denom3_1_witness a b) 0
  have h2 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom3_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom3_2_entire a b).analyticAt s) (denom3_2_witness a b) 0
  have h3 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom3_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom3_3_entire a b).analyticAt s) (denom3_3_witness a b) 0
  have h4 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom3_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom3_4_entire a b).analyticAt s) (denom3_4_witness a b) 0
  have h5 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom3_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom3_5_entire a b).analyticAt s) (denom3_5_witness a b) 0
  have h6 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom3_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom3_6_entire a b).analyticAt s) (denom3_6_witness a b) 0
  have h7 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom3_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom3_7_entire a b).analyticAt s) (denom3_7_witness a b) 0
  have h8 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom3_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom3_8_entire a b).analyticAt s) (denom3_8_witness a b) 0
  have h9 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom3_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom3_9_entire a b).analyticAt s) (denom3_9_witness a b) 0
  have h10 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom3_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom3_10_entire a b).analyticAt s) (denom3_10_witness a b) 0
  have hh : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom3_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom3_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom3_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom3_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom3_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom3_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom3_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom3_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom3_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom3_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom3_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
    filter_upwards [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10] with s hh0 hh1 hh2 hh3 hh4 hh5 hh6 hh7 hh8 hh9 hh10
    exact ⟨hh0,hh1,hh2,hh3,hh4,hh5,hh6,hh7,hh8,hh9,hh10⟩
  exact hh.exists
#print axioms denominators3_common

theorem denominators4_common (a b : ℂ) : ∃ s : ℂ,
    denom4_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom4_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom4_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom4_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom4_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom4_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom4_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom4_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom4_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom4_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom4_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  have h0 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom4_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom4_0_entire a b).analyticAt s) (denom4_0_witness a b) 0
  have h1 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom4_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom4_1_entire a b).analyticAt s) (denom4_1_witness a b) 0
  have h2 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom4_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom4_2_entire a b).analyticAt s) (denom4_2_witness a b) 0
  have h3 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom4_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom4_3_entire a b).analyticAt s) (denom4_3_witness a b) 0
  have h4 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom4_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom4_4_entire a b).analyticAt s) (denom4_4_witness a b) 0
  have h5 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom4_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom4_5_entire a b).analyticAt s) (denom4_5_witness a b) 0
  have h6 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom4_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom4_6_entire a b).analyticAt s) (denom4_6_witness a b) 0
  have h7 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom4_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom4_7_entire a b).analyticAt s) (denom4_7_witness a b) 0
  have h8 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom4_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom4_8_entire a b).analyticAt s) (denom4_8_witness a b) 0
  have h9 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom4_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom4_9_entire a b).analyticAt s) (denom4_9_witness a b) 0
  have h10 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom4_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom4_10_entire a b).analyticAt s) (denom4_10_witness a b) 0
  have hh : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom4_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom4_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom4_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom4_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom4_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom4_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom4_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom4_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom4_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom4_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom4_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
    filter_upwards [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10] with s hh0 hh1 hh2 hh3 hh4 hh5 hh6 hh7 hh8 hh9 hh10
    exact ⟨hh0,hh1,hh2,hh3,hh4,hh5,hh6,hh7,hh8,hh9,hh10⟩
  exact hh.exists
#print axioms denominators4_common

theorem denominators5_common (a b : ℂ) : ∃ s : ℂ,
    denom5_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom5_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom5_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom5_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom5_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom5_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom5_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom5_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom5_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom5_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom5_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  have h0 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom5_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom5_0_entire a b).analyticAt s) (denom5_0_witness a b) 0
  have h1 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom5_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom5_1_entire a b).analyticAt s) (denom5_1_witness a b) 0
  have h2 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom5_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom5_2_entire a b).analyticAt s) (denom5_2_witness a b) 0
  have h3 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom5_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom5_3_entire a b).analyticAt s) (denom5_3_witness a b) 0
  have h4 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom5_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom5_4_entire a b).analyticAt s) (denom5_4_witness a b) 0
  have h5 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom5_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom5_5_entire a b).analyticAt s) (denom5_5_witness a b) 0
  have h6 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom5_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom5_6_entire a b).analyticAt s) (denom5_6_witness a b) 0
  have h7 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom5_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom5_7_entire a b).analyticAt s) (denom5_7_witness a b) 0
  have h8 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom5_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom5_8_entire a b).analyticAt s) (denom5_8_witness a b) 0
  have h9 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom5_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom5_9_entire a b).analyticAt s) (denom5_9_witness a b) 0
  have h10 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom5_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom5_10_entire a b).analyticAt s) (denom5_10_witness a b) 0
  have hh : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom5_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom5_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom5_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom5_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom5_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom5_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom5_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom5_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom5_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom5_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom5_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
    filter_upwards [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10] with s hh0 hh1 hh2 hh3 hh4 hh5 hh6 hh7 hh8 hh9 hh10
    exact ⟨hh0,hh1,hh2,hh3,hh4,hh5,hh6,hh7,hh8,hh9,hh10⟩
  exact hh.exists
#print axioms denominators5_common

theorem denominators6_common (a b : ℂ) : ∃ s : ℂ,
    denom6_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom6_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom6_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom6_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom6_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom6_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom6_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom6_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom6_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom6_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom6_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  have h0 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom6_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom6_0_entire a b).analyticAt s) (denom6_0_witness a b) 0
  have h1 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom6_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom6_1_entire a b).analyticAt s) (denom6_1_witness a b) 0
  have h2 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom6_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom6_2_entire a b).analyticAt s) (denom6_2_witness a b) 0
  have h3 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom6_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom6_3_entire a b).analyticAt s) (denom6_3_witness a b) 0
  have h4 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom6_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom6_4_entire a b).analyticAt s) (denom6_4_witness a b) 0
  have h5 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom6_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom6_5_entire a b).analyticAt s) (denom6_5_witness a b) 0
  have h6 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom6_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom6_6_entire a b).analyticAt s) (denom6_6_witness a b) 0
  have h7 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom6_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom6_7_entire a b).analyticAt s) (denom6_7_witness a b) 0
  have h8 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom6_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom6_8_entire a b).analyticAt s) (denom6_8_witness a b) 0
  have h9 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom6_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom6_9_entire a b).analyticAt s) (denom6_9_witness a b) 0
  have h10 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom6_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom6_10_entire a b).analyticAt s) (denom6_10_witness a b) 0
  have hh : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom6_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom6_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom6_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom6_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom6_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom6_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom6_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom6_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom6_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom6_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom6_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
    filter_upwards [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10] with s hh0 hh1 hh2 hh3 hh4 hh5 hh6 hh7 hh8 hh9 hh10
    exact ⟨hh0,hh1,hh2,hh3,hh4,hh5,hh6,hh7,hh8,hh9,hh10⟩
  exact hh.exists
#print axioms denominators6_common

theorem denominators7_common (a b : ℂ) : ∃ s : ℂ,
    denom7_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom7_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom7_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom7_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom7_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom7_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom7_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom7_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom7_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom7_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧
    denom7_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
  have h0 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom7_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom7_0_entire a b).analyticAt s) (denom7_0_witness a b) 0
  have h1 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom7_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom7_1_entire a b).analyticAt s) (denom7_1_witness a b) 0
  have h2 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom7_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom7_2_entire a b).analyticAt s) (denom7_2_witness a b) 0
  have h3 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom7_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom7_3_entire a b).analyticAt s) (denom7_3_witness a b) 0
  have h4 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom7_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom7_4_entire a b).analyticAt s) (denom7_4_witness a b) 0
  have h5 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom7_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom7_5_entire a b).analyticAt s) (denom7_5_witness a b) 0
  have h6 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom7_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom7_6_entire a b).analyticAt s) (denom7_6_witness a b) 0
  have h7 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom7_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom7_7_entire a b).analyticAt s) (denom7_7_witness a b) 0
  have h8 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom7_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom7_8_entire a b).analyticAt s) (denom7_8_witness a b) 0
  have h9 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom7_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom7_9_entire a b).analyticAt s) (denom7_9_witness a b) 0
  have h10 : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom7_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 :=
    QuantitativeArithmeticEntireQuotient.nonzero_germ _
      (fun s => (denom7_10_entire a b).analyticAt s) (denom7_10_witness a b) 0
  have hh : ∀ᶠ s in 𝓝[≠] (0:ℂ), denom7_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom7_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom7_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom7_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom7_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom7_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom7_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom7_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom7_8 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom7_9 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 ∧ denom7_10 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b≠0 := by
    filter_upwards [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10] with s hh0 hh1 hh2 hh3 hh4 hh5 hh6 hh7 hh8 hh9 hh10
    exact ⟨hh0,hh1,hh2,hh3,hh4,hh5,hh6,hh7,hh8,hh9,hh10⟩
  exact hh.exists
#print axioms denominators7_common

end QuantitativeArithmeticSmallLevelThirtyFiveFullGrid
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveFullGridCaseIndexMatrixSeriesV4 -/
section
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option maxRecDepth 4000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace QuantitativeArithmeticSmallLevelThirtyFiveFullGrid
open Complex Matrix
def selectedLinearV3_0 (X Y Z W a b : ℂ) : (Fin 210→ℂ) →ₗ[ℂ] (Fin 210→ℂ) :=
  LinearMap.pi (fun i => match i.val/10 with
  | 0 => selectedPartLinear0_0 X Y Z W a b (i.val%10)
  | 1 => selectedPartLinear0_1 X Y Z W a b (i.val%10)
  | 2 => selectedPartLinear0_2 X Y Z W a b (i.val%10)
  | 3 => selectedPartLinear0_3 X Y Z W a b (i.val%10)
  | 4 => selectedPartLinear0_4 X Y Z W a b (i.val%10)
  | 5 => selectedPartLinear0_5 X Y Z W a b (i.val%10)
  | 6 => selectedPartLinear0_6 X Y Z W a b (i.val%10)
  | 7 => selectedPartLinear0_7 X Y Z W a b (i.val%10)
  | 8 => selectedPartLinear0_8 X Y Z W a b (i.val%10)
  | 9 => selectedPartLinear0_9 X Y Z W a b (i.val%10)
  | 10 => selectedPartLinear0_10 X Y Z W a b (i.val%10)
  | 11 => selectedPartLinear0_11 X Y Z W a b (i.val%10)
  | 12 => selectedPartLinear0_12 X Y Z W a b (i.val%10)
  | 13 => selectedPartLinear0_13 X Y Z W a b (i.val%10)
  | 14 => selectedPartLinear0_14 X Y Z W a b (i.val%10)
  | 15 => selectedPartLinear0_15 X Y Z W a b (i.val%10)
  | 16 => selectedPartLinear0_16 X Y Z W a b (i.val%10)
  | 17 => selectedPartLinear0_17 X Y Z W a b (i.val%10)
  | 18 => selectedPartLinear0_18 X Y Z W a b (i.val%10)
  | 19 => selectedPartLinear0_19 X Y Z W a b (i.val%10)
  | _ => selectedPartLinear0_20 X Y Z W a b (i.val%10))
theorem selectedLinearV3_0_apply (X Y Z W a b : ℂ) (v:Fin 210→ℂ) :
    selectedLinearV3_0 X Y Z W a b v = selectedRowsV3_0 X Y Z W a b v := by
  funext i
  dsimp only [selectedLinearV3_0,LinearMap.pi_apply,selectedRowsV3_0]
  split <;> simp_all [Nat.div_eq_of_lt,selectedPartLinear0_0,selectedPartLinear0_1,selectedPartLinear0_2,selectedPartLinear0_3,selectedPartLinear0_4,selectedPartLinear0_5,selectedPartLinear0_6,selectedPartLinear0_7,selectedPartLinear0_8,selectedPartLinear0_9,selectedPartLinear0_10,selectedPartLinear0_11,selectedPartLinear0_12,selectedPartLinear0_13,selectedPartLinear0_14,selectedPartLinear0_15,selectedPartLinear0_16,selectedPartLinear0_17,selectedPartLinear0_18,selectedPartLinear0_19,selectedPartLinear0_20]

def selectedMatrixV3_0 (X Y Z W a b : ℂ) : Matrix (Fin 210) (Fin 210) ℂ :=
  (selectedLinearV3_0 X Y Z W a b).toMatrix'

theorem selectedMatrixV3_0_mulVec (X Y Z W a b : ℂ) (v:Fin 210→ℂ) :
    selectedMatrixV3_0 X Y Z W a b *ᵥ v = selectedRowsV3_0 X Y Z W a b v := by
  rw [selectedMatrixV3_0,LinearMap.toMatrix'_mulVec,selectedLinearV3_0_apply]

theorem selectedMatrixV3_0_exists_nonsingular (a b : ℂ) : ∃ s : ℂ,
    (selectedMatrixV3_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b).det≠0 := by
  obtain ⟨s,hD0,hD1,hD2,hD3,hD4,hD5,hD6,hD7,hD8,hD9,hD10⟩ := denominators0_common a b
  refine ⟨s,?_⟩
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w hvw
  have hz : selectedMatrixV3_0 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b *ᵥ (v-w)=0 := by
    rw [Matrix.mulVec_sub,hvw,sub_self]
  rw [selectedMatrixV3_0_mulVec] at hz
  apply sub_eq_zero.mp
  exact selected_kernel_v3_case0 _ _ _ _ a b
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num : (2:ℂ)≠0)))
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num : (3:ℂ)≠0)))
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num : (5:ℂ)≠0)))
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num : (7:ℂ)≠0)))
    hD0 hD1 hD2 hD3 hD4 hD5 hD6 hD7 hD8 hD9 hD10 (v-w) hz
#print axioms selectedMatrixV3_0_exists_nonsingular


def selectedLinearV3_1 (X Y Z W a b : ℂ) : (Fin 210→ℂ) →ₗ[ℂ] (Fin 210→ℂ) :=
  LinearMap.pi (fun i => match i.val/10 with
  | 0 => selectedPartLinear1_0 X Y Z W a b (i.val%10)
  | 1 => selectedPartLinear1_1 X Y Z W a b (i.val%10)
  | 2 => selectedPartLinear1_2 X Y Z W a b (i.val%10)
  | 3 => selectedPartLinear1_3 X Y Z W a b (i.val%10)
  | 4 => selectedPartLinear1_4 X Y Z W a b (i.val%10)
  | 5 => selectedPartLinear1_5 X Y Z W a b (i.val%10)
  | 6 => selectedPartLinear1_6 X Y Z W a b (i.val%10)
  | 7 => selectedPartLinear1_7 X Y Z W a b (i.val%10)
  | 8 => selectedPartLinear1_8 X Y Z W a b (i.val%10)
  | 9 => selectedPartLinear1_9 X Y Z W a b (i.val%10)
  | 10 => selectedPartLinear1_10 X Y Z W a b (i.val%10)
  | 11 => selectedPartLinear1_11 X Y Z W a b (i.val%10)
  | 12 => selectedPartLinear1_12 X Y Z W a b (i.val%10)
  | 13 => selectedPartLinear1_13 X Y Z W a b (i.val%10)
  | 14 => selectedPartLinear1_14 X Y Z W a b (i.val%10)
  | 15 => selectedPartLinear1_15 X Y Z W a b (i.val%10)
  | 16 => selectedPartLinear1_16 X Y Z W a b (i.val%10)
  | 17 => selectedPartLinear1_17 X Y Z W a b (i.val%10)
  | 18 => selectedPartLinear1_18 X Y Z W a b (i.val%10)
  | 19 => selectedPartLinear1_19 X Y Z W a b (i.val%10)
  | _ => selectedPartLinear1_20 X Y Z W a b (i.val%10))
theorem selectedLinearV3_1_apply (X Y Z W a b : ℂ) (v:Fin 210→ℂ) :
    selectedLinearV3_1 X Y Z W a b v = selectedRowsV3_1 X Y Z W a b v := by
  funext i
  dsimp only [selectedLinearV3_1,LinearMap.pi_apply,selectedRowsV3_1]
  split <;> simp_all [Nat.div_eq_of_lt,selectedPartLinear1_0,selectedPartLinear1_1,selectedPartLinear1_2,selectedPartLinear1_3,selectedPartLinear1_4,selectedPartLinear1_5,selectedPartLinear1_6,selectedPartLinear1_7,selectedPartLinear1_8,selectedPartLinear1_9,selectedPartLinear1_10,selectedPartLinear1_11,selectedPartLinear1_12,selectedPartLinear1_13,selectedPartLinear1_14,selectedPartLinear1_15,selectedPartLinear1_16,selectedPartLinear1_17,selectedPartLinear1_18,selectedPartLinear1_19,selectedPartLinear1_20]

def selectedMatrixV3_1 (X Y Z W a b : ℂ) : Matrix (Fin 210) (Fin 210) ℂ :=
  (selectedLinearV3_1 X Y Z W a b).toMatrix'

theorem selectedMatrixV3_1_mulVec (X Y Z W a b : ℂ) (v:Fin 210→ℂ) :
    selectedMatrixV3_1 X Y Z W a b *ᵥ v = selectedRowsV3_1 X Y Z W a b v := by
  rw [selectedMatrixV3_1,LinearMap.toMatrix'_mulVec,selectedLinearV3_1_apply]

theorem selectedMatrixV3_1_exists_nonsingular (a b : ℂ) : ∃ s : ℂ,
    (selectedMatrixV3_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b).det≠0 := by
  obtain ⟨s,hD0,hD1,hD2,hD3,hD4,hD5,hD6,hD7,hD8,hD9,hD10⟩ := denominators1_common a b
  refine ⟨s,?_⟩
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w hvw
  have hz : selectedMatrixV3_1 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b *ᵥ (v-w)=0 := by
    rw [Matrix.mulVec_sub,hvw,sub_self]
  rw [selectedMatrixV3_1_mulVec] at hz
  apply sub_eq_zero.mp
  exact selected_kernel_v3_case1 _ _ _ _ a b
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num : (2:ℂ)≠0)))
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num : (3:ℂ)≠0)))
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num : (5:ℂ)≠0)))
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num : (7:ℂ)≠0)))
    hD0 hD1 hD2 hD3 hD4 hD5 hD6 hD7 hD8 hD9 hD10 (v-w) hz
#print axioms selectedMatrixV3_1_exists_nonsingular


def selectedMatrixV3_2 (X Y Z W a b : ℂ) : Matrix (Fin 210) (Fin 210) ℂ :=
  selectedMatrixV3_1 X Y (-Z) (-W) a b

theorem selectedMatrixV3_2_mulVec (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) :
    selectedMatrixV3_2 X Y Z W a b *ᵥ v = selectedRowsV3_2 X Y Z W a b v := by
  rw [selectedMatrixV3_2,selectedMatrixV3_1_mulVec]
  exact (rows2_sign_change X Y Z W a b hX hY hZ hW v).symm

theorem selectedMatrixV3_2_exists_nonsingular (a b : ℂ) : ∃ s : ℂ,
    (selectedMatrixV3_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b).det≠0 := by
  obtain ⟨s,hD0,hD1,hD2,hD3,hD4,hD5,hD6,hD7,hD8,hD9,hD10⟩ := denominators2_common a b
  have hX : (2:ℂ)^s≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hY : (3:ℂ)^s≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hZ : (5:ℂ)^s≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hW : (7:ℂ)^s≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  refine ⟨s,?_⟩
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w hvw
  have hz : selectedMatrixV3_2 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b *ᵥ (v-w)=0 := by
    rw [Matrix.mulVec_sub,hvw,sub_self]
  rw [selectedMatrixV3_2_mulVec _ _ _ _ a b hX hY hZ hW] at hz
  apply sub_eq_zero.mp
  exact selected_kernel_gauge_case2 _ _ _ _ a b hX hY hZ hW
    hD0 hD1 hD2 hD3 hD4 hD5 hD6 hD7 hD8 hD9 hD10 (v-w) hz
#print axioms selectedMatrixV3_2_exists_nonsingular


def selectedMatrixV3_3 (X Y Z W a b : ℂ) : Matrix (Fin 210) (Fin 210) ℂ :=
  selectedMatrixV3_0 X Y (-Z) (-W) a b

theorem selectedMatrixV3_3_mulVec (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) :
    selectedMatrixV3_3 X Y Z W a b *ᵥ v = selectedRowsV3_3 X Y Z W a b v := by
  rw [selectedMatrixV3_3,selectedMatrixV3_0_mulVec]
  exact (rows3_sign_change X Y Z W a b hX hY hZ hW v).symm

theorem selectedMatrixV3_3_exists_nonsingular (a b : ℂ) : ∃ s : ℂ,
    (selectedMatrixV3_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b).det≠0 := by
  obtain ⟨s,hD0,hD1,hD2,hD3,hD4,hD5,hD6,hD7,hD8,hD9,hD10⟩ := denominators3_common a b
  have hX : (2:ℂ)^s≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hY : (3:ℂ)^s≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hZ : (5:ℂ)^s≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hW : (7:ℂ)^s≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  refine ⟨s,?_⟩
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w hvw
  have hz : selectedMatrixV3_3 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b *ᵥ (v-w)=0 := by
    rw [Matrix.mulVec_sub,hvw,sub_self]
  rw [selectedMatrixV3_3_mulVec _ _ _ _ a b hX hY hZ hW] at hz
  apply sub_eq_zero.mp
  exact selected_kernel_gauge_case3 _ _ _ _ a b hX hY hZ hW
    hD0 hD1 hD2 hD3 hD4 hD5 hD6 hD7 hD8 hD9 hD10 (v-w) hz
#print axioms selectedMatrixV3_3_exists_nonsingular


def selectedMatrixV3_4 (X Y Z W a b : ℂ) : Matrix (Fin 210) (Fin 210) ℂ :=
  selectedMatrixV3_1 X Y Z (-W) a b

theorem selectedMatrixV3_4_mulVec (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) :
    selectedMatrixV3_4 X Y Z W a b *ᵥ v = selectedRowsV3_4 X Y Z W a b v := by
  rw [selectedMatrixV3_4,selectedMatrixV3_1_mulVec]
  exact (rows4_sign_change X Y Z W a b hX hY hZ hW v).symm

theorem selectedMatrixV3_4_exists_nonsingular (a b : ℂ) : ∃ s : ℂ,
    (selectedMatrixV3_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b).det≠0 := by
  obtain ⟨s,hD0,hD1,hD2,hD3,hD4,hD5,hD6,hD7,hD8,hD9,hD10⟩ := denominators4_common a b
  have hX : (2:ℂ)^s≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hY : (3:ℂ)^s≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hZ : (5:ℂ)^s≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hW : (7:ℂ)^s≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  refine ⟨s,?_⟩
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w hvw
  have hz : selectedMatrixV3_4 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b *ᵥ (v-w)=0 := by
    rw [Matrix.mulVec_sub,hvw,sub_self]
  rw [selectedMatrixV3_4_mulVec _ _ _ _ a b hX hY hZ hW] at hz
  apply sub_eq_zero.mp
  exact selected_kernel_gauge_case4 _ _ _ _ a b hX hY hZ hW
    hD0 hD1 hD2 hD3 hD4 hD5 hD6 hD7 hD8 hD9 hD10 (v-w) hz
#print axioms selectedMatrixV3_4_exists_nonsingular


def selectedMatrixV3_5 (X Y Z W a b : ℂ) : Matrix (Fin 210) (Fin 210) ℂ :=
  selectedMatrixV3_0 X Y Z (-W) a b

theorem selectedMatrixV3_5_mulVec (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) :
    selectedMatrixV3_5 X Y Z W a b *ᵥ v = selectedRowsV3_5 X Y Z W a b v := by
  rw [selectedMatrixV3_5,selectedMatrixV3_0_mulVec]
  exact (rows5_sign_change X Y Z W a b hX hY hZ hW v).symm

theorem selectedMatrixV3_5_exists_nonsingular (a b : ℂ) : ∃ s : ℂ,
    (selectedMatrixV3_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b).det≠0 := by
  obtain ⟨s,hD0,hD1,hD2,hD3,hD4,hD5,hD6,hD7,hD8,hD9,hD10⟩ := denominators5_common a b
  have hX : (2:ℂ)^s≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hY : (3:ℂ)^s≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hZ : (5:ℂ)^s≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hW : (7:ℂ)^s≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  refine ⟨s,?_⟩
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w hvw
  have hz : selectedMatrixV3_5 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b *ᵥ (v-w)=0 := by
    rw [Matrix.mulVec_sub,hvw,sub_self]
  rw [selectedMatrixV3_5_mulVec _ _ _ _ a b hX hY hZ hW] at hz
  apply sub_eq_zero.mp
  exact selected_kernel_gauge_case5 _ _ _ _ a b hX hY hZ hW
    hD0 hD1 hD2 hD3 hD4 hD5 hD6 hD7 hD8 hD9 hD10 (v-w) hz
#print axioms selectedMatrixV3_5_exists_nonsingular


def selectedMatrixV3_6 (X Y Z W a b : ℂ) : Matrix (Fin 210) (Fin 210) ℂ :=
  selectedMatrixV3_0 X Y (-Z) W a b

theorem selectedMatrixV3_6_mulVec (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) :
    selectedMatrixV3_6 X Y Z W a b *ᵥ v = selectedRowsV3_6 X Y Z W a b v := by
  rw [selectedMatrixV3_6,selectedMatrixV3_0_mulVec]
  exact (rows6_sign_change X Y Z W a b hX hY hZ hW v).symm

theorem selectedMatrixV3_6_exists_nonsingular (a b : ℂ) : ∃ s : ℂ,
    (selectedMatrixV3_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b).det≠0 := by
  obtain ⟨s,hD0,hD1,hD2,hD3,hD4,hD5,hD6,hD7,hD8,hD9,hD10⟩ := denominators6_common a b
  have hX : (2:ℂ)^s≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hY : (3:ℂ)^s≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hZ : (5:ℂ)^s≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hW : (7:ℂ)^s≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  refine ⟨s,?_⟩
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w hvw
  have hz : selectedMatrixV3_6 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b *ᵥ (v-w)=0 := by
    rw [Matrix.mulVec_sub,hvw,sub_self]
  rw [selectedMatrixV3_6_mulVec _ _ _ _ a b hX hY hZ hW] at hz
  apply sub_eq_zero.mp
  exact selected_kernel_gauge_case6 _ _ _ _ a b hX hY hZ hW
    hD0 hD1 hD2 hD3 hD4 hD5 hD6 hD7 hD8 hD9 hD10 (v-w) hz
#print axioms selectedMatrixV3_6_exists_nonsingular


def selectedMatrixV3_7 (X Y Z W a b : ℂ) : Matrix (Fin 210) (Fin 210) ℂ :=
  selectedMatrixV3_1 X Y (-Z) W a b

theorem selectedMatrixV3_7_mulVec (X Y Z W a b : ℂ) (hX:X≠0) (hY:Y≠0) (hZ:Z≠0) (hW:W≠0) (v:Fin 210→ℂ) :
    selectedMatrixV3_7 X Y Z W a b *ᵥ v = selectedRowsV3_7 X Y Z W a b v := by
  rw [selectedMatrixV3_7,selectedMatrixV3_1_mulVec]
  exact (rows7_sign_change X Y Z W a b hX hY hZ hW v).symm

theorem selectedMatrixV3_7_exists_nonsingular (a b : ℂ) : ∃ s : ℂ,
    (selectedMatrixV3_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b).det≠0 := by
  obtain ⟨s,hD0,hD1,hD2,hD3,hD4,hD5,hD6,hD7,hD8,hD9,hD10⟩ := denominators7_common a b
  have hX : (2:ℂ)^s≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hY : (3:ℂ)^s≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hZ : (5:ℂ)^s≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hW : (7:ℂ)^s≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  refine ⟨s,?_⟩
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w hvw
  have hz : selectedMatrixV3_7 ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) a b *ᵥ (v-w)=0 := by
    rw [Matrix.mulVec_sub,hvw,sub_self]
  rw [selectedMatrixV3_7_mulVec _ _ _ _ a b hX hY hZ hW] at hz
  apply sub_eq_zero.mp
  exact selected_kernel_gauge_case7 _ _ _ _ a b hX hY hZ hW
    hD0 hD1 hD2 hD3 hD4 hD5 hD6 hD7 hD8 hD9 hD10 (v-w) hz
#print axioms selectedMatrixV3_7_exists_nonsingular

end QuantitativeArithmeticSmallLevelThirtyFiveFullGrid
end
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveFullGridAllCasesV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveFullGrid
open Complex Matrix

/-- The eight explicit sign cases, in the order of the algebraic certificates. -/
def selectedMatrixCase (c : Fin 8) (X Y Z W a b : ℂ) :
    Matrix (Fin 210) (Fin 210) ℂ :=
  match c.val with
  | 0 => selectedMatrixV3_0 X Y Z W a b
  | 1 => selectedMatrixV3_1 X Y Z W a b
  | 2 => selectedMatrixV3_2 X Y Z W a b
  | 3 => selectedMatrixV3_3 X Y Z W a b
  | 4 => selectedMatrixV3_4 X Y Z W a b
  | 5 => selectedMatrixV3_5 X Y Z W a b
  | 6 => selectedMatrixV3_6 X Y Z W a b
  | _ => selectedMatrixV3_7 X Y Z W a b

def selectedRowsCase (c : Fin 8) (X Y Z W a b : ℂ)
    (v : Fin 210 → ℂ) : Fin 210 → ℂ :=
  match c.val with
  | 0 => selectedRowsV3_0 X Y Z W a b v
  | 1 => selectedRowsV3_1 X Y Z W a b v
  | 2 => selectedRowsV3_2 X Y Z W a b v
  | 3 => selectedRowsV3_3 X Y Z W a b v
  | 4 => selectedRowsV3_4 X Y Z W a b v
  | 5 => selectedRowsV3_5 X Y Z W a b v
  | 6 => selectedRowsV3_6 X Y Z W a b v
  | _ => selectedRowsV3_7 X Y Z W a b v

theorem selectedMatrixCase_mulVec (c : Fin 8) (X Y Z W a b : ℂ)
    (hX : X ≠ 0) (hY : Y ≠ 0) (hZ : Z ≠ 0) (hW : W ≠ 0)
    (v : Fin 210 → ℂ) :
    selectedMatrixCase c X Y Z W a b *ᵥ v = selectedRowsCase c X Y Z W a b v := by
  fin_cases c
  · exact selectedMatrixV3_0_mulVec X Y Z W a b v
  · exact selectedMatrixV3_1_mulVec X Y Z W a b v
  · exact selectedMatrixV3_2_mulVec X Y Z W a b hX hY hZ hW v
  · exact selectedMatrixV3_3_mulVec X Y Z W a b hX hY hZ hW v
  · exact selectedMatrixV3_4_mulVec X Y Z W a b hX hY hZ hW v
  · exact selectedMatrixV3_5_mulVec X Y Z W a b hX hY hZ hW v
  · exact selectedMatrixV3_6_mulVec X Y Z W a b hX hY hZ hW v
  · exact selectedMatrixV3_7_mulVec X Y Z W a b hX hY hZ hW v

/-- The two good-prime parameters are unrestricted, including zero. -/
theorem selectedMatrixCase_exists_nonsingular (c : Fin 8) (a b : ℂ) :
    ∃ s : ℂ, (selectedMatrixCase c
      ((2 : ℂ)^s) ((3 : ℂ)^s) ((5 : ℂ)^s) ((7 : ℂ)^s) a b).det ≠ 0 := by
  fin_cases c
  · exact selectedMatrixV3_0_exists_nonsingular a b
  · exact selectedMatrixV3_1_exists_nonsingular a b
  · exact selectedMatrixV3_2_exists_nonsingular a b
  · exact selectedMatrixV3_3_exists_nonsingular a b
  · exact selectedMatrixV3_4_exists_nonsingular a b
  · exact selectedMatrixV3_5_exists_nonsingular a b
  · exact selectedMatrixV3_6_exists_nonsingular a b
  · exact selectedMatrixV3_7_exists_nonsingular a b

/-- Translation to the exponent used by the actual additive Mellin system. -/
theorem selectedMatrixCase_shifted_exists_nonsingular
    (c : Fin 8) (a b μ : ℂ) :
    ∃ s : ℂ, (selectedMatrixCase c
      ((2 : ℂ)^(s-μ)) ((3 : ℂ)^(s-μ))
      ((5 : ℂ)^(s-μ)) ((7 : ℂ)^(s-μ)) a b).det ≠ 0 := by
  obtain ⟨s, hs⟩ := selectedMatrixCase_exists_nonsingular c a b
  refine ⟨s+μ, ?_⟩
  simpa only [add_sub_cancel_right] using hs

#print axioms selectedMatrixCase_mulVec
#print axioms selectedMatrixCase_exists_nonsingular
#print axioms selectedMatrixCase_shifted_exists_nonsingular
end QuantitativeArithmeticSmallLevelThirtyFiveFullGrid
end
end
