module

public import QuantitativeMaassEulerFourierV1
public import FinitenessRamanujanFourierV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology ComplexConjugate

namespace QuantitativeMaass

open FinitenessRamanujanSum

theorem eulerPhase_translate_positive (q n a : ℕ) (x : ℝ) :
    Complex.exp (((2*Real.pi*(n:ℝ)*(x+(a:ℝ)/q):ℝ):ℂ)*Complex.I)=
      phase q n a*Complex.exp (((2*Real.pi*(n:ℝ)*x:ℝ):ℂ)*Complex.I) := by
  unfold phase
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring

theorem eulerPhase_translate_negative (q n a : ℕ) (x : ℝ) :
    Complex.exp (-(((2*Real.pi*(n:ℝ)*(x+(a:ℝ)/q):ℝ):ℂ)*Complex.I))=
      conj (phase q n a)*Complex.exp (-(((2*Real.pi*(n:ℝ)*x:ℝ):ℂ)*Complex.I)) := by
  unfold phase
  rw [←Complex.exp_conj,←Complex.exp_add]
  congr 1
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I]
  push_cast
  ring

/-- The same real Ramanujan coefficient multiplies both Fourier signs,
using the proved conjugation invariance of the primitive exponential sum. -/
theorem eulerParityPhase_ramanujan (q n σ : ℕ) (x : ℝ) :
    (∑ a ∈ residues q,eulerParityPhase σ n (x+(a:ℝ)/q))=
      complexSum q n*eulerParityPhase σ n x := by
  simp_rw [eulerParityPhase,eulerPhase_translate_positive,eulerPhase_translate_negative]
  rw [Finset.sum_add_distrib,←Finset.sum_mul,←Finset.mul_sum,←Finset.sum_mul,←map_sum]
  change complexSum q n*Complex.exp (((2*Real.pi*(n:ℝ)*x:ℝ):ℂ)*Complex.I)+
      (-1:ℂ)^σ*(conj (complexSum q n)*Complex.exp (-(((2*Real.pi*(n:ℝ)*x:ℝ):ℂ)*Complex.I)))=_
  rw [conjugate_sum]
  ring

theorem principalEulerTerm_twisted (b : ℕ → ℂ) (r : ℝ) (σ q n : ℕ) (x y : ℝ) :
    principalEulerTerm (FinitenessRamanujanFourier.twisted b q) r σ n (x,y)=
      ∑ a ∈ residues q,principalEulerTerm b r σ n (x+(a:ℝ)/q,y) := by
  unfold principalEulerTerm FinitenessRamanujanFourier.twisted
  dsimp only
  rw [←Finset.mul_sum,eulerParityPhase_ramanujan,ofReal_ramanujan]
  ring

#print axioms eulerPhase_translate_positive
#print axioms eulerPhase_translate_negative
#print axioms eulerParityPhase_ramanujan
#print axioms principalEulerTerm_twisted

end QuantitativeMaass
