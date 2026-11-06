module

public import AsymptoticFoldedTerminalV1
public import FinitenessGlobalHeightV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticFoldSelection

open UpperHalfPlane Set AsymptoticHyperbolicSlash AsymptoticReconstructionBranch
open AsymptoticFoldedLow

variable {L : ℝ} (hL : 0<L) (b d : ℝ)

theorem fold_action (n : ℤ) (z : ℍ) :
    ((fold hL b d n • z:ℍ):ℂ)=((branch L b d hL.ne' • z:ℍ):ℂ)-(n:ℂ) := by
  rw [fold,branch_action hL,branch_action hL]
  push_cast
  ring

theorem fold_im (n : ℤ) (z : ℍ) :
    (fold hL b d n • z).im=(branch L b d hL.ne' • z).im := by
  simpa using congrArg Complex.im (fold_action hL b d n z)

theorem fold_re (n : ℤ) (z : ℍ) :
    (fold hL b d n • z).re=(branch L b d hL.ne' • z).re-(n:ℝ) := by
  simpa using congrArg Complex.re (fold_action hL b d n z)

theorem fold_phase (n : ℤ) (k : ℕ) (z : ℍ) :
    phase (fold hL b d n) k z=phase (branch L b d hL.ne') k z := rfl

/-- There is exactly one contributing fold into the half-open strip. -/
theorem fold_mem_strip_iff (n : ℤ) (z : ℍ) :
    fold hL b d n • z∈AsymptoticMassTransport.strip ↔
      n=Int.floor (branch L b d hL.ne' • z).re := by
  change (0≤(fold hL b d n • z).re ∧ (fold hL b d n • z).re<1) ↔ _
  rw [fold_re hL b d]
  rw [eq_comm,Int.floor_eq_iff]
  constructor <;> intro hn <;> constructor <;> linarith [hn.1,hn.2]

theorem periodic_fold (F : ℂ → ℂ) (hp : ∀ z,F (z+1)=F z) (n : ℤ) (z : ℍ) :
    F (fold hL b d n • z:ℍ)=F (branch L b d hL.ne' • z:ℍ) := by
  rw [fold_action hL b d]
  have hp' : Function.Periodic F (1:ℂ) := hp
  simpa using (hp'.zsmul n).sub_eq ((branch L b d hL.ne' • z:ℍ):ℂ)

/-- The complete integer sum reduces to the unique strip representative;
no inverse images are discarded in defining the operator. -/
theorem strip_tsum (G : ℤ → ℂ) (z : ℍ) :
    (∑' n : ℤ, (AsymptoticMassTransport.strip).indicator
      (fun _ : ℍ => G n) (fold hL b d n • z))=
        G (Int.floor (branch L b d hL.ne' • z).re) := by
  classical
  let n₀ : ℤ := Int.floor (branch L b d hL.ne' • z).re
  rw [tsum_eq_single n₀]
  · exact Set.indicator_of_mem ((fold_mem_strip_iff hL b d n₀ z).mpr rfl) _
  · intro n hn
    exact Set.indicator_of_notMem ((fold_mem_strip_iff hL b d n z).not.mpr hn) _

#print axioms fold_mem_strip_iff
#print axioms periodic_fold
#print axioms strip_tsum

end AsymptoticFoldSelection
