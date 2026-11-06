module

public import QuantitativeSpectralExceptionalGeneratorRowsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalReducedRows

open UpperHalfPlane ContinuousLinearMap AsymptoticCompactBranch
open QuantitativeSpectralExceptionalUnweight (G Space)
open scoped MatrixGroups lp

/-- The unweighting map is independent of its compactness metadata, so
any proved reciprocal-cap estimate bounds the actual operator. -/
theorem unweight_norm_of_bound {s : Set ℍ} {ε P : ℝ} (hε : 0<ε) (t : ℕ)
    (D : QuantitativeSpectralExceptionalUnweight.Data s ε t) (hP : 0≤P)
    (hbound : ∀ z∈s, (cap ε t z)⁻¹≤P) (x : ℍ) :
    ‖QuantitativeSpectralExceptionalUnweight.unweight hε t D x‖≤P := by
  let D' : QuantitativeSpectralExceptionalUnweight.Data s ε t := ⟨P,hP,hbound⟩
  have he : QuantitativeSpectralExceptionalUnweight.unweight hε t D x =
      QuantitativeSpectralExceptionalUnweight.unweight hε t D' x := by
    apply ContinuousLinearMap.ext
    intro v
    apply lp.ext
    rfl
  rw [he]
  exact QuantitativeSpectralExceptionalUnweight.unweight_norm hε t D' x

/-- A transport is bounded by the reciprocal cap at its actual image;
the original cap is at most one. -/
theorem transport_norm_of_inverse (a : SL(2,ℤ)) {s : Set ℍ} (hs : IsCompact s)
    {ε P : ℝ} (hε : 0<ε) (t : ℕ) (hP : 0≤P)
    (hbound : ∀ z∈s, (cap ε t (AsymptoticCongruenceLabels.integralLabel a • z))⁻¹≤P)
    (x : ℍ) : ‖QuantitativeSpectralDefectCocycle.transport a hs hε t x‖≤P := by
  classical
  let g := AsymptoticRationalFreeness.realMatrix (AsymptoticCongruenceLabels.rationalGL a)
  have hc : ∀ z, ‖coefficient g s ε t z‖≤P := by
    intro z
    by_cases hz : z∈s
    · rw [coefficient,Set.indicator_of_mem hz,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (ratio_pos g hε t z)]
      have he : g • z = AsymptoticCongruenceLabels.integralLabel a • z :=
        (AsymptoticRationalBranches.ofMatrix_action _ (AsymptoticCongruenceLabels.rationalGL_positive a) z).symm
      have hn : cap ε t z≤1 :=
        pow_le_one₀ (le_of_lt (lt_min (div_pos z.im_pos hε) zero_lt_one)) (min_le_right _ _)
      unfold ratio
      apply (div_le_div_of_nonneg_right hn (cap_pos hε t _).le).trans
      simpa only [one_div,he] using hbound z hz
    · rw [coefficient,Set.indicator_of_notMem hz,norm_zero]
      exact hP
  let T := AsymptoticOrbitBranch.operator (AsymptoticCongruenceLabels.integralLabel a)
    (coefficient g s ε t) hP hc x
  have he : QuantitativeSpectralDefectCocycle.transport a hs hε t x=T := by
    apply ContinuousLinearMap.ext
    intro v
    apply lp.ext
    rfl
  rw [he]
  exact AsymptoticOrbitBranch.operator_norm_le _ _ hP hc x

/-- One common image-cap bound gives a linear-in-word-length bound on
the exact recombining operator itself, for arbitrary residual data. -/
theorem wordRecombine_norm_of_inverse (A : Finset SL(2,ℤ)) (l : List SL(2,ℤ))
    (hl : ∀ a∈l, a∈A) {s : Set ℍ} (hs : IsCompact s)
    {ε P : ℝ} (hε : 0<ε) (t : ℕ) (hP : 0≤P)
    (hbound : ∀ k : ℕ, ∀ z∈s,
      (cap ε t (AsymptoticCongruenceLabels.integralLabel (l.drop k).prod • z))⁻¹≤P)
    (x : ℍ) : ‖wordRecombine A hs hε t x l hl‖≤l.length*P := by
  induction l with
  | nil => simp only [wordRecombine,norm_zero,List.length_nil,Nat.cast_zero,zero_mul,le_refl]
  | cons a l ih =>
    have ht : ∀ k : ℕ, ∀ z∈s,
        (cap ε t (AsymptoticCongruenceLabels.integralLabel (l.drop k).prod • z))⁻¹≤P := by
      intro k z hz
      simpa only [List.drop_succ_cons] using hbound (k+1) z hz
    apply opNorm_le_bound _ (by positivity)
    intro v
    rw [wordRecombine,_root_.add_apply]
    apply (norm_add_le _ _).trans
    have hi := (wordRecombine A hs hε t x l
      (fun c hc => hl c (List.mem_cons_of_mem a hc))).le_of_opNorm_le
      (ih (fun c hc => hl c (List.mem_cons_of_mem a hc)) ht) v
    have hc := (AsymptoticOrbitDiagonal.corner (QuantitativeSpectralDefectCocycle.image l.prod s) x).le_of_opNorm_le
      (AsymptoticOrbitRegion.corner_norm_le _ _) (v (some ⟨a,hl a List.mem_cons_self⟩))
    simp only [one_mul] at hc
    have hb := (QuantitativeSpectralDefectCocycle.transport l.prod hs hε t x).le_of_opNorm_le
      (transport_norm_of_inverse l.prod hs hε t hP (by simpa using ht 0) x)
      (AsymptoticOrbitDiagonal.corner (QuantitativeSpectralDefectCocycle.image l.prod s) x
        (v (some ⟨a,hl a List.mem_cons_self⟩)))
    have hv := hc.trans (PiLp.norm_apply_le v (some ⟨a,hl a List.mem_cons_self⟩))
    have hh := add_le_add hi (hb.trans (mul_le_mul_of_nonneg_left hv hP))
    apply hh.trans_eq
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    ring

#print axioms unweight_norm_of_bound
#print axioms transport_norm_of_inverse
#print axioms wordRecombine_norm_of_inverse

end QuantitativeSpectralExceptionalReducedRows
