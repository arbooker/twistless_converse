module

public import SmallLevelTwentyOneRawWordRatesV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Matrix SmallLevelNormalized SmallLevelGenerators ModularGroup
open scoped MatrixGroups

def integerSeed : Fin 4 → Matrix (Fin 2) (Fin 2) ℤ
  | 0 => !![1,1;0,1]
  | 1 => !![1,0;21,1]
  | 2 => !![2,-1;-21,11]
  | _ => !![0,-1;21,0]

def integerRaw : Word → Matrix (Fin 2) (Fin 2) ℤ
  | .one => 1
  | .generator i => integerSeed i
  | .mul u v => integerRaw u*integerRaw v
  | .inv w => (integerRaw w).adjugate

theorem rawSeed_integer (i : Fin 4) : rawSeed i=(integerSeed i).map (Int.castRingHom ℝ) := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [rawSeed,integerSeed,seed,SpecialLinearGroup.toGL,
      SpecialLinearGroup.map_apply_coe,SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two,Matrix.inv_def,Matrix.det_fin_two,SmallLevelGenerators.oddMatrix,SmallLevelGenerators.lower,
      ModularGroup.T,Matrix.map_apply]

/-- The integer word calculation is an exact representative of the analytic
matrix, including inverse words. -/
theorem raw_integer (w : Word) : raw w=(integerRaw w).map (Int.castRingHom ℝ) := by
  induction w with
  | one => simp [raw,integerRaw]
  | generator i => exact rawSeed_integer i
  | mul u v hu hv =>
    simp only [raw,integerRaw,hu,hv]
    ext i j
    simp [Matrix.mul_apply,Fin.sum_univ_two]
  | inv w hw =>
    simp only [raw,integerRaw,hw]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.adjugate_fin_two,Matrix.map_apply]

/-- Character bookkeeping is just the parity of the Fricke letters. -/
def frickeCount : Word → ℕ
  | .one => 0
  | .generator i => if i=3 then 1 else 0
  | .mul u v => frickeCount u+frickeCount v
  | .inv w => frickeCount w

theorem character_count (χ : ℂ) (w : Word) : character χ w=χ^(frickeCount w) := by
  induction w with
  | one => simp [character,frickeCount]
  | generator i => by_cases hi : i=3 <;> simp [character,seedSign,frickeCount,hi]
  | mul u v hu hv => simp only [character,frickeCount,pow_add,hu,hv]
  | inv w hw => exact hw

#print axioms rawSeed_integer
#print axioms raw_integer
#print axioms character_count
end SmallLevelTwentyOneKnownWords
