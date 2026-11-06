module

/- Periodic integer-indexed vectors are exactly Q finite coordinates. -/
public import SpanningTraceAlgebraV1

@[expose] public section

namespace SpanningCyclicCoordinates
open SpanningTraceAlgebra
variable {F : Type*}

def residue {Q : ℕ} (hQ : 0<Q) (j : ℤ) : Fin Q :=
  ⟨(j%(Q:ℤ)).toNat,by
    have h0 : 0≤j%(Q:ℤ) := Int.emod_nonneg _ (by exact_mod_cast (Nat.ne_of_gt hQ))
    have h1 : j%(Q:ℤ)<Q := Int.emod_lt_of_pos _ (by exact_mod_cast hQ)
    omega⟩

def extend {Q : ℕ} (hQ : 0<Q) (f : Fin Q → F) : ℤ → F := fun j => f (residue hQ j)
def coordinates {Q : ℕ} (v : ℤ → F) : Fin Q → F := fun a => v a

theorem extend_cyclic {Q : ℕ} (hQ : 0<Q) (f : Fin Q → F) : Cyclic Q (extend hQ f) := by
  intro j
  apply congrArg f
  apply Fin.ext
  simp [residue]

theorem cyclic_shift_nat {Q : ℕ} {v : ℤ → F} (hv : Cyclic Q v) (n : ℕ) :
    ∀ j, v (j+(n:ℤ)*Q)=v j := by
  induction n with
  | zero => simp
  | succ n ih =>
    intro j
    have he : j+(n+1:ℕ)*Q=(j+(n:ℤ)*Q)+Q := by push_cast; ring
    rw [he,hv,ih]

theorem cyclic_shift_int {Q : ℕ} {v : ℤ → F} (hv : Cyclic Q v) (n j : ℤ) :
    v (j+n*Q)=v j := by
  cases n with
  | ofNat n => exact cyclic_shift_nat hv n j
  | negSucc n =>
    have hh := cyclic_shift_nat hv (n+1) (j+Int.negSucc n*Q)
    have he : j+Int.negSucc n*Q+(n+1:ℕ)*Q=j := by
      change j+(-(n+1:ℕ):ℤ)*Q+(n+1:ℕ)*Q=j
      ring
    rw [he] at hh
    exact hh.symm

theorem cyclic_emod {Q : ℕ} {v : ℤ → F} (hv : Cyclic Q v) (j : ℤ) : v (j%Q)=v j := by
  have he := cyclic_shift_int hv (-(j/(Q:ℤ))) j
  simpa only [Int.emod_def,sub_eq_add_neg,neg_mul,mul_neg,mul_comm] using he

theorem coordinates_extend {Q : ℕ} (hQ : 0<Q) (f : Fin Q → F) :
    coordinates (extend hQ f)=f := by
  funext a
  apply congrArg f
  apply Fin.ext
  dsimp [residue]
  rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast a.isLt)]
  rfl

theorem extend_coordinates {Q : ℕ} (hQ : 0<Q) {v : ℤ → F} (hv : Cyclic Q v) :
    extend hQ (coordinates v)=v := by
  funext j
  dsimp [extend,coordinates,residue]
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast (Nat.ne_of_gt hQ)))]
  exact cyclic_emod hv j

def coordinatesEquiv {Q : ℕ} (hQ : 0<Q) : (Fin Q → F) ≃ {v : ℤ → F // Cyclic Q v} where
  toFun f := ⟨extend hQ f,extend_cyclic hQ f⟩
  invFun v := coordinates v.val
  left_inv f := coordinates_extend hQ f
  right_inv v := Subtype.ext (extend_coordinates hQ v.property)

#print axioms coordinatesEquiv

end SpanningCyclicCoordinates
