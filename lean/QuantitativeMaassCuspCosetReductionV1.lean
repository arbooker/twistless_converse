module

public import QuantitativeMaassHeckeTreeReductionV1

set_option autoImplicit false
@[expose] public noncomputable section

open Matrix
open scoped Matrix

namespace QuantitativeMaass

variable {F : Type*} [Field F]

/-- Reductions modulo p of the adjugates of the p+1 representatives
D_p and [[1,Nj],[0,p]], with n the nonzero reduction of N. -/
def cuspAdjMod (n : F) (j : Option F) : Matrix (Fin 2) (Fin 2) F :=
  match j with
  | none => !![1,0;0,0]
  | some u => !![0,-n*u;0,1]

theorem cuspAdjMod_none_zero_iff (n a b c d : F) :
    !![a,b;c,d] * cuspAdjMod n none = 0 ↔ a=0 ∧ c=0 := by
  constructor
  · intro h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) h
    have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 0) h
    constructor
    · simpa [cuspAdjMod, Matrix.mul_apply, Fin.sum_univ_two] using h00
    · simpa [cuspAdjMod, Matrix.mul_apply, Fin.sum_univ_two] using h10
  · rintro ⟨rfl,rfl⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cuspAdjMod, Matrix.mul_apply, Fin.sum_univ_two]

theorem cuspAdjMod_some_zero_iff (n a b c d u : F) :
    !![a,b;c,d] * cuspAdjMod n (some u) = 0 ↔ b=a*n*u ∧ d=c*n*u := by
  simp only [cuspAdjMod, Matrix.mul_fin_two]
  constructor
  · intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) h
    have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 1) h
    change a * (-n*u) + b*1 = 0 at h01
    change c * (-n*u) + d*1 = 0 at h11
    constructor
    · linear_combination h01
    · linear_combination h11
  · rintro ⟨hb,hd⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb,hd] <;> ring

/-- Every nonzero singular 2x2 matrix has exactly one kernel line from the
actual unramified representative family. This is the finite-field input
for all-cusp Hecke equivariance. -/
theorem cuspAdjMod_unique (n a b c d : F) (hn : n≠0)
    (hM : ¬(a=0 ∧ b=0 ∧ c=0 ∧ d=0)) (hdet : a*d-b*c=0) :
    ∃! j : Option F, !![a,b;c,d] * cuspAdjMod n j = 0 := by
  by_cases ha : a=0
  · by_cases hc : c=0
    · refine ⟨none,(cuspAdjMod_none_zero_iff n a b c d).mpr ⟨ha,hc⟩,?_⟩
      intro j hj
      cases j with
      | none => rfl
      | some u =>
        obtain ⟨hb,hd⟩ := (cuspAdjMod_some_zero_iff n a b c d u).mp hj
        exact (hM ⟨ha,by simpa [ha] using hb,hc,by simpa [hc] using hd⟩).elim
    · have hb : b=0 := by
        apply (mul_eq_zero.mp (show b*c=0 by simpa [ha] using hdet.symm)).resolve_right hc
      let u := d/(c*n)
      have hu : d=c*n*u := by dsimp [u]; field_simp [hc,hn]
      refine ⟨some u,(cuspAdjMod_some_zero_iff n a b c d u).mpr ⟨by simp [ha,hb],hu⟩,?_⟩
      intro j hj
      cases j with
      | none => exact (hc ((cuspAdjMod_none_zero_iff n a b c d).mp hj).2).elim
      | some v =>
        congr 1
        have hv := ((cuspAdjMod_some_zero_iff n a b c d v).mp hj).2
        exact mul_left_cancel₀ (mul_ne_zero hc hn) (hv.symm.trans hu)
  · let u := b/(a*n)
    have hu : b=a*n*u := by dsimp [u]; field_simp [ha,hn]
    have hd : d=c*n*u := by
      dsimp [u]
      field_simp [ha,hn]
      linear_combination hdet
    refine ⟨some u,(cuspAdjMod_some_zero_iff n a b c d u).mpr ⟨hu,hd⟩,?_⟩
    intro j hj
    cases j with
    | none => exact (ha ((cuspAdjMod_none_zero_iff n a b c d).mp hj).1).elim
    | some v =>
      congr 1
      have hv := ((cuspAdjMod_some_zero_iff n a b c d v).mp hj).1
      exact mul_left_cancel₀ (mul_ne_zero ha hn) (hv.symm.trans hu)

#print axioms cuspAdjMod_unique

end QuantitativeMaass
