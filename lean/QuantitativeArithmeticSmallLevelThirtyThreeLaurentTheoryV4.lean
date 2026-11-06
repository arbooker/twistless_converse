module

public import QuantitativeArithmeticCompact33VerificationV1
public import QuantitativeArithmeticSevenLaurentSignCovarianceV1
public import QuantitativeArithmeticSmallLevelThirtyThreeFullMatricesV1
public import QuantitativeArithmeticSmallLevelThirtyThreeLaurentDataV1
public import QuantitativeArithmeticSmallLevelThirtyThreeMinusFullKernelV1
public import QuantitativeArithmeticSmallLevelThirtyThreePlusFullKernelV1

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelThirtyThreeLaurent. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelThirtyThreeSourceMatchV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

/-! Alternate provider: replace the old ThirtyThreeSourceMatch import with
this module. Do not import both providers, since their public declarations
intentionally have the same names and types. No original source is edited. -/

namespace QuantitativeArithmeticSmallLevelThirtyThreeLaurent

open QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open SmallLevelPrimeRates

theorem source_match (x y z η a u v : ℂ) (w : Fin 66→ℂ) (i : Fin 775) :
    eval x y z η a u v (fun j => w (gridIndex (j:ℤ))) (sourceRows i)=
      laurentRows x y z η a u v w (sourceKind i) := by
  rw [← QuantitativeArithmeticCompact33.compiled_eq_source i]
  exact QuantitativeArithmeticCompact33.normalized_compile_correct x y z η a u v w _

theorem physical_source_match (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    (ε s : ℂ) (hε : ε=1 ∨ ε= -1) (w : Fin 66→ℂ) (i : Fin 775) :
    eval (parameter 2 m s) (parameter 3 m s) (parameter 11 m s)
      (phase m ε) (badParameter f 2) (badParameter f 3) (badParameter f 11)
      (fun j => w (gridIndex (j:ℤ))) (sourceRows i)=
      gridLeadingRows m f ε s w (sourceKind i) := by
  rw [source_match,leadingRows_laurent m hf ε s hε w (sourceKind i)]

#print axioms source_match
#print axioms physical_source_match

end QuantitativeArithmeticSmallLevelThirtyThreeLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyThreeSignCovarianceV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeLaurent
open QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelThirtyThreeKnownWords (GridSource)

theorem source_compatible (i : Fin 775) :
    (sourceRows i).all (fun t => decide (SignCompatible t.2.2))=true := by
  fin_cases i <;> decide +kernel

theorem source_sign_covariance (x y z η a u v : ℂ) (w : ℕ→ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) (i : Fin 775) :
    eval x y z η a u v w (sourceRows i)=
      eval x (u*y) (v*z) (η*u*v) a 1 1 w (sourceRows i) := by
  apply eval_sign_covariance x y z η a u v w hu hv
  intro t ht
  have hh := List.all_eq_true.mp (source_compatible i) t ht
  exact of_decide_eq_true hh

#print axioms source_sign_covariance
end QuantitativeArithmeticSmallLevelThirtyThreeLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyThreePhysicalRankV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeLaurent
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open SmallLevelPrimeRates Matrix

theorem all_signs_kernel (x y z η a u v : ℂ) (w : ℕ→ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hη : η=1 ∨ η= -1) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hd : QuantitativeArithmeticSmallLevelThirtyThreeMinor.determinant x (u*y) a≠0)
    (hsource : ∀ i : Fin 775,eval x y z η a u v w (sourceRows i)=0) :
    ∀ j<66,w j=0 := by
  have hu0 : u≠0 := by rcases hu with h|h <;> simp [h]
  have hv0 : v≠0 := by rcases hv with h|h <;> simp [h]
  have hc : η*u*v=1 ∨ η*u*v= -1 := by
    rcases hη with hη|hη <;> rcases hu with hu|hu <;> rcases hv with hv|hv <;> simp [hη,hu,hv]
  have hscaled (i : Fin 775) : eval x (u*y) (v*z) (η*u*v) a 1 1 w (sourceRows i)=0 := by
    rw [← source_sign_covariance x y z η a u v w hu hv i]
    exact hsource i
  have hb (σ : ℚ) (hσ : (σ:ℂ)=η*u*v) (j : ℕ) :
      eval x (u*y) (v*z) 1 a 1 1 w (baseRows σ j)=0 := by
    by_cases hj : j<775
    · have hh := baseRows_eval x (u*y) (v*z) a σ w ⟨j,hj⟩
      rw [hσ] at hh
      exact hh.trans (hscaled ⟨j,hj⟩)
    · simp only [baseRows,dite_eq_right hj,eval_nil]
  rcases hc with hc|hc
  · exact QuantitativeArithmeticSmallLevelThirtyThreePlusElimination.full_kernel_zero
      x (u*y) (v*z) a w hx (mul_ne_zero hu0 hy) (mul_ne_zero hv0 hz) hd
      (hb 1 (by simpa only [Rat.cast_one] using hc.symm))
  · exact QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination.full_kernel_zero
      x (u*y) (v*z) a w hx (mul_ne_zero hu0 hy) (mul_ne_zero hv0 hz) hd
      (hb (-1) (by simpa only [Rat.cast_neg,Rat.cast_one] using hc.symm))

theorem gridIndex_fin (j : Fin 66) : gridIndex (j:ℕ)=j := by
  apply Fin.ext
  change ((j:ℕ)% (66:ℤ)).toNat=j.val
  rw [Int.emod_eq_of_lt (by exact_mod_cast Nat.zero_le j.val) (by exact_mod_cast j.isLt)]
  simp

/-- One point of full rank for the original system, for every auxiliary eigenvalue. -/
theorem original_full_rank (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    (ε : ℂ) (hε : ε=1 ∨ ε= -1) :
    ∃ s : ℂ,∀ w : Fin 66→ℂ,fullLeadingMatrix m f ε s *ᵥ w=0 → w=0 := by
  have hu := badParameter_three_sign hf.toEulerData
  have hv := badParameter_eleven_sign hf.toEulerData
  have hu0 : badParameter f 3≠0 := by rcases hu with h|h <;> simp [h]
  obtain ⟨s,hs⟩ := QuantitativeArithmeticSmallLevelThirtyThreeMinor.determinant_not_identically_zero
    (badParameter f 2) (badParameter f 3) hu0 m
  refine ⟨s,?_⟩
  intro w hw
  rw [fullLeadingMatrix_mulVec] at hw
  have hsource (i : Fin 775) :
      eval (parameter 2 m s) (parameter 3 m s) (parameter 11 m s)
        (phase m ε) (badParameter f 2) (badParameter f 3) (badParameter f 11)
        (fun j => w (gridIndex (j:ℤ))) (sourceRows i)=0 := by
    rw [physical_source_match m hf ε s hε w i,hw]
    rfl
  have hh := all_signs_kernel _ _ _ _ _ _ _ _
    (parameter_ne_zero 2 m (by decide) s) (parameter_ne_zero 3 m (by decide) s)
    (parameter_ne_zero 11 m (by decide) s) (grid_physical_sign m hε) hu hv hs hsource
  funext j
  simpa only [gridIndex_fin,Pi.zero_apply] using hh j.val j.isLt

#print axioms all_signs_kernel
#print axioms original_full_rank
end QuantitativeArithmeticSmallLevelThirtyThreeLaurent
end
end
