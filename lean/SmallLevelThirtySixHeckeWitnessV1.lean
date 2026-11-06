module

public import SmallLevelThirtySixWitnessV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace SmallLevelThirtySix

open UpperHalfPlane ModularGroup Matrix
open scoped ModularForm MatrixGroups

def heckeFinite (j : ℤ) : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mkOfDetNeZero !![1,6*j;0,5] (by norm_num [det_fin_two])

def heckeInfinity : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mkOfDetNeZero !![5,0;0,1] (by norm_num [det_fin_two])

theorem heckeFinite_det (j : ℤ) : (heckeFinite j).det.val=5 := by
  change det !![(1:ℝ),6*j;0,5]=5
  norm_num [det_fin_two]

theorem heckeInfinity_det : heckeInfinity.det.val=5 := by
  change det !![(5:ℝ),0;0,1]=5
  norm_num [det_fin_two]

/-- The Hecke branches are fixed individually by the witness permutation. -/
theorem finite_intertwining (j : ℤ) :
    heckeFinite j*(witness : GL (Fin 2) ℝ)=
      (witnessFinite j : GL (Fin 2) ℝ)*heckeFinite j := by
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [heckeFinite, witness, witnessFinite, GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL, SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem infinity_intertwining :
    heckeInfinity*(witness : GL (Fin 2) ℝ)=
      (witnessInfinity : GL (Fin 2) ℝ)*heckeInfinity := by
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [heckeInfinity, witness, witnessInfinity, GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL, SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem finite_scalar (k : ℤ) (j : ℤ) (g : ℍ → ℂ) (c : ℂ) :
    (c • g) ∣[k] heckeFinite j=c • (g ∣[k] heckeFinite j) := by
  rw [ModularForm.smul_slash]
  congr 1
  simp only [UpperHalfPlane.σ, heckeFinite_det]
  norm_num

theorem infinity_scalar (k : ℤ) (g : ℍ → ℂ) (c : ℂ) :
    (c • g) ∣[k] heckeInfinity=c • (g ∣[k] heckeInfinity) := by
  rw [ModularForm.smul_slash]
  congr 1
  simp only [UpperHalfPlane.σ, heckeInfinity_det]
  norm_num

def heckeFive (k : ℤ) (g : ℍ → ℂ) : ℍ → ℂ :=
  (g ∣[k] heckeInfinity)+(g ∣[k] heckeFinite 0)+(g ∣[k] heckeFinite 1)+
    (g ∣[k] heckeFinite 2)+(g ∣[k] heckeFinite 3)+(g ∣[k] heckeFinite 4)

/-- Exact obstruction identity from the Hecke eigenrelation and the seven
checked matrix words. No nonzero-eigenvalue hypothesis is used. -/
theorem obstruction_hecke (m : ℕ) (g : ℍ → ℂ) (lam : ℂ)
    (hT : (g ∣[((2*m:ℕ):ℤ)] T) ∣[((2*m:ℕ):ℤ)] T=(g ∣[((2*m:ℕ):ℤ)] T)-g)
    (hS : g ∣[((2*m:ℕ):ℤ)] S = -g)
    (he : heckeFive ((2*m:ℕ):ℤ) g=lam • g) :
    (obstruction m g ∣[((2*m:ℕ):ℤ)] heckeInfinity)-
      (2:ℂ) • (obstruction m g ∣[((2*m:ℕ):ℤ)] heckeFinite 1)+
      (obstruction m g ∣[((2*m:ℕ):ℤ)] heckeFinite 2)-
      (obstruction m g ∣[((2*m:ℕ):ℤ)] heckeFinite 3)+
      (obstruction m g ∣[((2*m:ℕ):ℤ)] heckeFinite 4)+lam • obstruction m g=0 := by
  have hh := congrArg (fun f : ℍ → ℂ => f ∣[((2*m:ℕ):ℤ)] witness) he
  simp only [heckeFive, SlashAction.add_slash, ModularForm.SL_smul_slash] at hh
  have hf (j : ℤ) :
      (g ∣[((2*m:ℕ):ℤ)] heckeFinite j) ∣[((2*m:ℕ):ℤ)] witness=
      (g ∣[((2*m:ℕ):ℤ)] witnessFinite j) ∣[((2*m:ℕ):ℤ)] heckeFinite j := by
    simp only [ModularForm.SL_slash, ← SlashAction.slash_mul, finite_intertwining]
  have hi : (g ∣[((2*m:ℕ):ℤ)] heckeInfinity) ∣[((2*m:ℕ):ℤ)] witness=
      (g ∣[((2*m:ℕ):ℤ)] witnessInfinity) ∣[((2*m:ℕ):ℤ)] heckeInfinity := by
    simp only [ModularForm.SL_slash, ← SlashAction.slash_mul, infinity_intertwining]
  rw [hi, hf 0, hf 1, hf 2, hf 3, hf 4, infinity_action m g hT hS,
    finite_zero_action m g hT hS, finite_one_action m g hT hS,
    finite_two_action m g hT hS, finite_three_action m g hT hS,
    finite_four_action m g hT hS, witness_action m g hT hS] at hh
  simp only [SlashAction.add_slash, finite_scalar, infinity_scalar] at hh
  funext z
  have hhz := congrFun hh z
  have hez := congrFun he z
  simp only [heckeFive, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hhz hez
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  linear_combination (hhz-hez)/2

#print axioms finite_intertwining
#print axioms infinity_intertwining
#print axioms obstruction_hecke

end SmallLevelThirtySix
