module

public import QuantitativeMaassHilbertSchmidtV1
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal

namespace QuantitativeMaass

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Nonnegative Hilbert energy is allowed to be infinite. -/
def extendedHilbertEnergy (b : HilbertBasis ι ℂ H) (B : H →L[ℂ] H) : ℝ≥0∞ :=
  ∑' i,ENNReal.ofReal (‖B (b i)‖^2)

omit [CompleteSpace H] in
theorem extendedParseval (b : HilbertBasis ι ℂ H) (x : H) :
    ENNReal.ofReal (‖x‖^2)=∑' i,ENNReal.ofReal (‖inner ℂ x (b i)‖^2) := by
  have h := hasSum_inner_norm_sq b x
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) h.summable,h.tsum_eq]

/-- Adjoint invariance without a Hilbert--Schmidt finiteness premise.
The only interchange is Tonelli for nonnegative extended-real series. -/
theorem extendedHilbertEnergy_adjoint (b : HilbertBasis ι ℂ H) (B : H →L[ℂ] H) :
    extendedHilbertEnergy b B.adjoint=extendedHilbertEnergy b B := by
  unfold extendedHilbertEnergy
  simp_rw [extendedParseval b,B.adjoint_inner_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro j
  apply tsum_congr
  intro i
  rw [norm_inner_symm]

/-- The positive square root converts a quadratic form to square norm. -/
theorem positive_sqrt_norm_square (D : H →L[ℂ] H) (hD : 0≤D) (v : H) :
    ‖CFC.sqrt D v‖^2=(inner ℂ (D v) v).re := by
  have hS : IsSelfAdjoint (CFC.sqrt D) :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg D)).isSelfAdjoint
  have he : CFC.sqrt D (CFC.sqrt D v)=D v :=
    congrArg (fun T : H →L[ℂ] H => T v) (CFC.sqrt_mul_sqrt_self D hD)
  have hi := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hS (CFC.sqrt D v) v
  change inner ℂ (CFC.sqrt D (CFC.sqrt D v)) v=inner ℂ (CFC.sqrt D v) (CFC.sqrt D v) at hi
  rw [he] at hi
  calc
    _ = (inner ℂ (CFC.sqrt D v) (CFC.sqrt D v)).re :=
      (inner_self_eq_norm_sq (𝕜:=ℂ) (CFC.sqrt D v)).symm
    _ = _ := congrArg Complex.re hi.symm

/-- A self-adjoint smoothing and positive filter admit the exact
quadratic-trace/filtered-energy interchange, including infinite values. -/
theorem positive_smoothed_energy (b : HilbertBasis ι ℂ H)
    (K D : H →L[ℂ] H) (hK : IsSelfAdjoint K) (hD : 0≤D) :
    (∑' i,ENNReal.ofReal ((inner ℂ (D (K (b i))) (K (b i))).re))=
      extendedHilbertEnergy b (K.comp (CFC.sqrt D)) := by
  have hS : IsSelfAdjoint (CFC.sqrt D) :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg D)).isSelfAdjoint
  have he := extendedHilbertEnergy_adjoint b ((CFC.sqrt D).comp K)
  rw [ContinuousLinearMap.adjoint_comp,hK.adjoint_eq,hS.adjoint_eq] at he
  rw [he]
  unfold extendedHilbertEnergy
  apply tsum_congr
  intro i
  simp only [ContinuousLinearMap.comp_apply,positive_sqrt_norm_square D hD]

#print axioms extendedParseval
#print axioms extendedHilbertEnergy_adjoint
#print axioms positive_sqrt_norm_square
#print axioms positive_smoothed_energy

end QuantitativeMaass
