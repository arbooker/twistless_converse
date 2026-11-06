module

public import QuantitativeSpectralFiniteReductionV1
public import AsymptoticCongruenceDefectV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralDefectCocycle

open Matrix UpperHalfPlane MeasureTheory ContinuousLinearMap
open AsymptoticCongruenceLabels AsymptoticRationalBranches AsymptoticRationalFreeness
open AsymptoticRegularCompactBranch (Space)
open AsymptoticCompactBranch AsymptoticOrbitDecode
open scoped MatrixGroups lp

abbrev G := AsymptoticRationalGroup.Group

def image (B : SL(2,ℤ)) (s : Set ℍ) : Set ℍ := (fun z => integralLabel B • z) '' s

theorem image_compact (B : SL(2,ℤ)) {s : Set ℍ} (hs : IsCompact s) :
    IsCompact (image B s) := hs.image (action_continuous _)

/-- Full-orbit transport of a defect, with no periodic refolding of its
output. This distinction is needed for exact generator telescoping. -/
def transport (B : SL(2,ℤ)) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ) (x : ℍ) : Space →L[ℂ] Space :=
  AsymptoticOrbitBranch.operator (integralLabel B)
    (coefficient (realMatrix (rationalGL B)) s ε t)
    (data (realMatrix (rationalGL B)) hs hε t).bound_nonneg
    (coefficient_norm_le _ hε t (data _ hs hε t)) x

theorem transport_apply (B : SL(2,ℤ)) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ) (x : ℍ) (v : Space) (g : G) :
    transport B hs hε t x v g =
      coefficient (realMatrix (rationalGL B)) s ε t (g • x)*v (integralLabel B*g) := rfl

theorem transport_norm (B : SL(2,ℤ)) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ) (x : ℍ) :
    ‖transport B hs hε t x‖ ≤ (data (realMatrix (rationalGL B)) hs hε t).bound :=
  AsymptoticOrbitBranch.operator_norm_le _ _ _ _ _

/-- Exact multiplicative cocycle for the literal weighted compact
congruence defects. It supplies finite-word observability without
assuming approximate invariance under an entire congruence group. -/
theorem defect_mul (A B : SL(2,ℤ)) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ) (x : ℍ) :
    AsymptoticCongruenceDefect.operator (A*B) hs hε t x =
      AsymptoticCongruenceDefect.operator B hs hε t x +
      (transport B hs hε t x).comp
        (AsymptoticCongruenceDefect.operator A (image_compact B hs) hε t x) := by
  classical
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext g
  simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,lp.coeFn_add,Pi.add_apply,transport_apply,
    AsymptoticCongruenceDefect.operator_decode,map_mul,mul_assoc]
  by_cases hg : g • x ∈ s
  · have hBg : (integralLabel B*g) • x ∈ image B s :=
      ⟨g • x,hg,(mul_smul _ _ _).symm⟩
    simp only [ite_eq_left hg,ite_eq_left hBg,coefficient,Set.indicator_of_mem hg,ratio,
      Complex.ofReal_div]
    have hact : realMatrix (rationalGL B) • (g • x) = (integralLabel B*g) • x := by
      rw [mul_smul]
      exact (ofMatrix_action _ (rationalGL_positive B) _).symm
    rw [hact]
    field_simp [cap_ne_zero hε t ((integralLabel B*g) • x)]
    ring
  · simp only [ite_eq_right hg,coefficient,Set.indicator_of_notMem hg,zero_mul,add_zero]

theorem defect_mul_norm (A B : SL(2,ℤ)) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ) (x : ℍ) (v : Space) :
    ‖AsymptoticCongruenceDefect.operator (A*B) hs hε t x v‖ ≤
      ‖AsymptoticCongruenceDefect.operator B hs hε t x v‖ +
      (data (realMatrix (rationalGL B)) hs hε t).bound *
        ‖AsymptoticCongruenceDefect.operator A (image_compact B hs) hε t x v‖ := by
  rw [defect_mul,_root_.add_apply,ContinuousLinearMap.comp_apply]
  exact (norm_add_le _ _).trans (add_le_add le_rfl
    ((transport B hs hε t x).le_of_opNorm_le (transport_norm B hs hε t x) _))

#print axioms defect_mul
#print axioms defect_mul_norm

end QuantitativeSpectralDefectCocycle
