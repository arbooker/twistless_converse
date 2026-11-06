module

public import SmallLevelTwentyOnePoleFullRowsV1

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
@[expose] public section
namespace SmallLevelTwentyOneKnownWords

def augmentedTaylorSpecs : Fin 72 → ℕ × ℤ × ℤ :=
  ![(1,1,84), (1,-1,84), (1,2,84), (1,-2,84), (1,3,84), (1,-3,84), (1,4,84), (1,-4,84), (1,6,84), (1,-6,84), (1,7,84), (1,-7,84), (1,12,84), (1,-12,84), (1,14,84), (1,-14,84), (1,21,84), (1,-21,84), (1,28,84), (1,-28,84), (1,42,84), (1,-42,84), (1,84,84), (1,-84,84), (2,1,21), (2,-1,21), (2,3,21), (2,-3,21), (2,7,21), (2,-7,21), (2,21,21), (2,-21,21), (3,1,28), (3,-1,28), (3,2,28), (3,-2,28), (3,4,28), (3,-4,28), (3,7,28), (3,-7,28), (3,14,28), (3,-14,28), (3,28,28), (3,-28,28), (6,1,7), (6,-1,7), (6,7,7), (6,-7,7), (7,1,12), (7,-1,12), (7,2,12), (7,-2,12), (7,3,12), (7,-3,12), (7,4,12), (7,-4,12), (7,6,12), (7,-6,12), (7,12,12), (7,-12,12), (14,1,3), (14,-1,3), (14,3,3), (14,-3,3), (21,1,4), (21,-1,4), (21,2,4), (21,-2,4), (21,4,4), (21,-4,4), (42,1,1), (42,-1,1)]

theorem augmentedTaylorSpecs_valid : ∀ i,
    0<(augmentedTaylorSpecs i).1 ∧ (augmentedTaylorSpecs i).1∣42 ∧
    (augmentedTaylorSpecs i).2.1≠0 ∧
    (Nat.lcm 21 ((augmentedTaylorSpecs i).1^2):ℤ)*(augmentedTaylorSpecs i).2.2=(42:ℤ)^2 ∧
    (augmentedTaylorSpecs i).2.1∣(augmentedTaylorSpecs i).2.2 := by decide

def augmentedEntireSpecs : Fin 8 → ℕ := ![1,2,3,6,7,14,21,42]

theorem augmentedEntireSpecs_valid : ∀ i, 0<augmentedEntireSpecs i ∧ augmentedEntireSpecs i∣42 := by decide

def augmentedHeckeSpecs : Fin 41 → ℕ × ℤ :=
  ![(2,0), (2,1), (2,2), (2,3), (2,4), (2,5), (2,6), (2,7), (2,8), (2,9), (2,10), (2,11), (2,12), (2,13), (2,14), (2,15), (2,16), (2,17), (2,18), (2,19), (2,20), (3,0), (3,1), (3,2), (3,3), (3,4), (3,5), (3,6), (3,7), (3,8), (3,9), (3,10), (3,11), (3,12), (3,13), (7,0), (7,1), (7,2), (7,3), (7,4), (7,5)]

theorem augmentedHeckeSpecs_valid : ∀ i,
    (augmentedHeckeSpecs i).1.Prime ∧ (augmentedHeckeSpecs i).1∣42 := by decide

#print axioms augmentedTaylorSpecs_valid
#print axioms augmentedEntireSpecs_valid
#print axioms augmentedHeckeSpecs_valid
end SmallLevelTwentyOneKnownWords
