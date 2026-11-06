module

public import SmallLevelSignedFrickeV1
public import SmallLevelThirtySixFourierV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace SmallLevelEvenScale

open Complex UpperHalfPlane ModularGroup SmallLevelGenerators
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open QuantitativeArithmeticRetainedReconstruction
open scoped MatrixGroups ModularForm

def scaledFourier (k : ℕ) (f : ℕ → ℂ) (z : ℂ) : ℂ :=
  fourier (fullCoefficients f k) (z/2)

def scaledFunction (k : ℕ) (f : ℕ → ℂ) (z : ℍ) : ℂ := scaledFourier k f z

theorem scaled_antiperiod {L : ℕ} {f : ℕ → ℂ} (hf : EulerData (4*L) f)
    (k : ℕ) {z : ℂ} (hz : 0<z.im) : scaledFourier k f (z+1)= -scaledFourier k f z := by
  have hh := SmallLevelThirtySix.square_prime_average_zero hf (p:=2) (by decide)
    (show 2^2∣4*L from ⟨L,rfl⟩) k
    (z:=z/2) (by simpa using div_pos hz (by norm_num : (0:ℝ)<2))
  norm_num [completeTwist, Finset.sum_range_succ] at hh
  dsimp only [scaledFourier]
  rw [show (z+1)/2=z/2+(1:ℂ)/2 by ring]
  linear_combination hh

theorem scaled_fricke {L k : ℕ} (hL : 0<L) {f : ℕ → ℂ}
    (hf : IsSolution (4*L) k f) :
    ∃ χ : ℂ, ∀ z : ℂ, 0<z.im → scaledFourier k f z=
      χ/(((Real.sqrt L:ℂ)*z)^k)*scaledFourier k f (-1/((L:ℂ)*z)) := by
  obtain ⟨χ, _, hfr⟩ := FinitenessOriginalFricke.solution_fricke (by omega : 0<4*L) hf
  refine ⟨χ,fun z hz => ?_⟩
  have he := hfr (z/2) (by simpa using div_pos hz (by norm_num : (0:ℝ)<2))
  have hsqrt : Real.sqrt (4*L:ℕ)=2*Real.sqrt (L:ℝ) := by
    rw [Nat.cast_mul, Real.sqrt_mul (by norm_num)]
    norm_num
  rw [hsqrt] at he
  norm_num only [Nat.cast_mul, Nat.cast_ofNat, ofReal_mul, ofReal_ofNat] at he
  rw [show (2*(Real.sqrt L:ℂ))*(z/2)=(Real.sqrt L:ℂ)*z by ring,
    show -1/((4*(L:ℂ))*(z/2))=(-1/((L:ℂ)*z))/2 by ring] at he
  exact he

theorem scaled_T {L k : ℕ} {f : ℕ → ℂ} (hf : EulerData (4*L) f) :
    scaledFunction k f ∣[(k:ℤ)] T= -scaledFunction k f := by
  funext z
  rw [ModularForm.SL_slash_apply, modular_T_smul]
  have hd : denom T z=1 := by simp [ModularGroup.denom_apply, ModularGroup.T]
  rw [hd, one_zpow, mul_one]
  simpa only [scaledFunction, coe_vadd, Complex.ofReal_one, add_comm, Pi.neg_apply]
    using scaled_antiperiod hf k z.im_pos

theorem scaled_lower {L k : ℕ} (hL : 0<L) {f : ℕ → ℂ}
    (hf : IsSolution (4*L) k f) :
    scaledFunction k f ∣[(k:ℤ)] lower L= -scaledFunction k f := by
  obtain ⟨χ,hfr⟩ := scaled_fricke hL hf
  have hp (z : ℂ) (hz : 0<z.im) :
      scaledFourier k f (z-1)=(-1:ℂ)*scaledFourier k f z := by
    have hh := scaled_antiperiod hf.toEulerData k
      (z:=z-1) (by simpa using hz)
    rw [sub_add_cancel] at hh
    linear_combination hh
  change (fun z : ℍ => scaledFourier k f z) ∣[(k:ℤ)] lower L=
    -(fun z : ℍ => scaledFourier k f z)
  simpa only [neg_one_smul] using lower_eigen_of_fricke hL _ χ (-1) hp hfr

#print axioms scaled_antiperiod
#print axioms scaled_fricke
#print axioms scaled_T
#print axioms scaled_lower

end SmallLevelEvenScale
