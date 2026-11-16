module

public import QuantitativeMaassDistributionExpInverseV1
public import Mathlib.Analysis.SpecialFunctions.Exponential

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace QuantitativeMaass

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem operatorPower_apply_norm_le (B : H →L[ℝ] H) (v : H) (n : ℕ) :
    ‖(B^n) v‖≤‖B‖^n*‖v‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',mul_apply_eq_comp]
    calc
      _ ≤ ‖B‖*‖(B^n) v‖ := B.le_opNorm _
      _ ≤ ‖B‖*(‖B‖^n*‖v‖) := mul_le_mul_of_nonneg_left ih (norm_nonneg _)
      _ = _ := by rw [pow_succ']; ring

variable [CompleteSpace H]

/-- Evolution with the sign appropriate to the tested distribution equation
T(phi')=B T(phi): the pointwise equation is u'=-B u. -/
def boundedExpEvolution (B : H →L[ℝ] H) (v : H) (t : ℝ) : H :=
  NormedSpace.exp (t • (-B)) v

theorem boundedExpEvolution_hasSum (B : H →L[ℝ] H) (v : H) (t : ℝ) :
    HasSum (fun n : ℕ => ((-1:ℝ)^n*(n.factorial:ℝ)⁻¹) • (t^n • (B^n) v))
      (boundedExpEvolution B v t) := by
  have h := (ContinuousLinearMap.apply ℝ H v).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂:=ℝ) (t • (-B)))
  have he : t • (-B)=(-t) • B := by simp only [smul_neg,neg_smul]
  convert! h using 1
  funext n
  change ((-1:ℝ)^n*(n.factorial:ℝ)⁻¹) • (t^n • (B^n) v)=
    ((n.factorial:ℝ)⁻¹ • (t • (-B))^n) v
  rw [he,smul_pow]
  simp only [smul_apply,smul_smul]
  rw [neg_pow]
  congr 1
  ring

theorem boundedExpEvolution_hasDerivAt (B : H →L[ℝ] H) (v : H) (t : ℝ) :
    HasDerivAt (boundedExpEvolution B v) (-B (boundedExpEvolution B v t)) t := by
  have h := (hasDerivAt_exp_smul_const' (-B) t).clm_apply (hasDerivAt_const t v)
  change HasDerivAt (fun s => NormedSpace.exp (s • (-B)) v)
    (-B (NormedSpace.exp (t • (-B)) v)) t
  simpa only [mul_apply_eq_comp,neg_apply,map_zero,add_zero] using h

theorem boundedExpEvolution_continuous (B : H →L[ℝ] H) (v : H) :
    Continuous (boundedExpEvolution B v) :=
  continuous_iff_continuousAt.mpr (fun t => (boundedExpEvolution_hasDerivAt B v t).continuousAt)

omit [CompleteSpace H] in
theorem boundedExpEvolution_zero (B : H →L[ℝ] H) (v : H) : boundedExpEvolution B v 0=v := by
  simp only [boundedExpEvolution,zero_smul,NormedSpace.exp_zero,one_apply_eq_self]

#print axioms boundedExpEvolution_hasSum
#print axioms boundedExpEvolution_hasDerivAt
#print axioms boundedExpEvolution_zero

end QuantitativeMaass
