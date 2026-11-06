module

public import QuantitativeSpectralExceptionalWordResidualsV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalReducedRows

open UpperHalfPlane ContinuousLinearMap AsymptoticObservationStack
open QuantitativeSpectralExceptionalUnweight (G Space)
open QuantitativeSpectralWordDefect
open scoped MatrixGroups lp

abbrev GeneratorData (A : Finset SL(2,ℤ)) := PiLp 2 (fun _ : Option ↥A => Space)

/-- One literal residual row and the actual signed-generator residuals on
a common compact region. There are no long-word rows in this stack. -/
def generatorRows (A : Finset SL(2,ℤ)) (L : Space →L[ℂ] Space)
    {u : Set ℍ} (hu : IsCompact u) {ε : ℝ} (hε : 0 < ε) (t : ℕ) (x : ℍ) :
    Option ↥A → Space →L[ℂ] Space
  | none => L
  | some a => AsymptoticCongruenceDefect.operator a.val hu hε t x

theorem generator_projection (A : Finset SL(2,ℤ)) (L : Space →L[ℂ] Space)
    {u : Set ℍ} (hu : IsCompact u) {ε : ℝ} (hε : 0 < ε) (t : ℕ) (x : ℍ) (a : ↥A) :
    (PiLp.proj 2 (fun _ : Option ↥A => Space) (some a)).comp
      (stack (generatorRows A L hu hε t x)) = AsymptoticCongruenceDefect.operator a.val hu hε t x := by
  apply ContinuousLinearMap.ext
  intro v
  rfl

/-- Explicit finite-word telescoping map, recursively built from actual
transport operators and single-generator coordinate projections. -/
def wordRecombine (A : Finset SL(2,ℤ)) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ) (x : ℍ) :
    (l : List SL(2,ℤ)) → (∀ a ∈ l, a ∈ A) → GeneratorData A →L[ℂ] Space
  | [],_ => 0
  | a::l,hl => wordRecombine A hs hε t x l (fun c hc => hl c (List.mem_cons_of_mem a hc)) +
      (QuantitativeSpectralDefectCocycle.transport l.prod hs hε t x).comp
        ((AsymptoticOrbitDiagonal.corner (QuantitativeSpectralDefectCocycle.image l.prod s) x).comp
          (PiLp.proj 2 (fun _ : Option ↥A => Space) (some ⟨a,hl a List.mem_cons_self⟩)))

/-- The telescope evaluates to the actual word defect on the original
compact source, by the exact multiplicative defect cocycle. -/
theorem wordRecombine_stack (A : Finset SL(2,ℤ)) (L : Space →L[ℂ] Space)
    (l : List SL(2,ℤ)) (hl : ∀ a ∈ l, a ∈ A)
    {s u : Set ℍ} (hs : IsCompact s) (hu : IsCompact u) (hsub : region l s ⊆ u)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ) (x : ℍ) :
    (wordRecombine A hs hε t x l hl).comp (stack (generatorRows A L hu hε t x)) =
      AsymptoticCongruenceDefect.operator l.prod hs hε t x := by
  induction l with
  | nil => simp only [wordRecombine,zero_comp,List.prod_nil,defect_one]
  | cons a l ih =>
    rw [wordRecombine,add_comp,List.prod_cons,QuantitativeSpectralDefectCocycle.defect_mul]
    rw [ih (fun c hc => hl c (List.mem_cons_of_mem a hc)) (fun z hz => hsub (Or.inl hz))]
    simp only [comp_assoc,generator_projection]
    rw [defect_restrict (QuantitativeSpectralDefectCocycle.image_compact l.prod hs) hu
      (fun z hz => hsub (Or.inr hz)) a hε t x]

/-- The exact telescoping operator has the same fixed-word transport
bound as the norm-level telescope, without residual-smallness premises. -/
theorem wordRecombine_norm (A : Finset SL(2,ℤ)) (l : List SL(2,ℤ))
    (hl : ∀ a ∈ l, a ∈ A) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ) (x : ℍ) :
    ‖wordRecombine A hs hε t x l hl‖ ≤ cost l hs hε t := by
  induction l with
  | nil => simp only [wordRecombine,norm_zero,cost,le_refl]
  | cons a l ih =>
    apply opNorm_le_bound _ (cost_nonneg _ hs hε t)
    intro v
    rw [wordRecombine,_root_.add_apply]
    apply (norm_add_le _ _).trans
    have hi := (wordRecombine A hs hε t x l
      (fun c hc => hl c (List.mem_cons_of_mem a hc))).le_of_opNorm_le
      (ih (fun c hc => hl c (List.mem_cons_of_mem a hc))) v
    have hc := (AsymptoticOrbitDiagonal.corner (QuantitativeSpectralDefectCocycle.image l.prod s) x).le_of_opNorm_le
      (AsymptoticOrbitRegion.corner_norm_le _ _) (v (some ⟨a,hl a List.mem_cons_self⟩))
    simp only [one_mul] at hc
    have ht := (QuantitativeSpectralDefectCocycle.transport l.prod hs hε t x).le_of_opNorm_le
      (QuantitativeSpectralDefectCocycle.transport_norm l.prod hs hε t x)
      (AsymptoticOrbitDiagonal.corner (QuantitativeSpectralDefectCocycle.image l.prod s) x
        (v (some ⟨a,hl a List.mem_cons_self⟩)))
    have hv := hc.trans (PiLp.norm_apply_le v (some ⟨a,hl a List.mem_cons_self⟩))
    have hh := ht.trans (mul_le_mul_of_nonneg_left hv
      (AsymptoticCompactBranch.data _ hs hε t).bound_nonneg)
    simpa only [comp_apply,PiLp.proj_apply,cost,add_mul] using add_le_add hi hh

#print axioms wordRecombine_stack
#print axioms wordRecombine_norm

end QuantitativeSpectralExceptionalReducedRows
